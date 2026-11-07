import PRZZProductSummation
import PRZZMollifiedTime
import PRZZSourceWOuter
import PRZZReplacementMass
import PRZZOptimalOuter

/-! Weighted cutoff removal for the actual V-W series. The time majorant
is summable before any arithmetic cutoff is chosen. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Set Filter Topology Complex
namespace XiPrime8845.PRZZProductTime
open PRZZLocalReplacement PRZZL1Finite
set_option maxHeartbeats 3000000

theorem term_measurable (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hab : a+b ≠ 0) (T : ℝ) (hT : 0 < T) (m k : ℕ)
    (hm : 1 ≤ m) (hk : 1 ≤ k) :
    AEStronglyMeasurable (fun t => directTerm a b (fun n t => error a b n t) t m k)
      (volume.restrict (Icc T (2*T))) := by
  have har := (abs_le.mp ((Complex.abs_re_le_norm a).trans ha)).1
  have hbr := (abs_le.mp ((Complex.abs_re_le_norm b).trans hb)).1
  have hx : 0 < ((m*k:ℕ):ℝ) := by positivity
  have hw : ContinuousOn (fun t : ℝ => PRZZDyadicEnvelope.sourceW (a+b)
      (((m*k:ℕ):ℝ)/(t/(2*Real.pi)))) (Icc T (2*T)) := by
    apply (PRZZSourceWOuter.sourceW_continuous (a+b) hab).comp
    · fun_prop (disch := intro t ht; have : 0 < t := hT.trans_le ht.1; positivity)
    · intro t ht
      have : 0 < t := hT.trans_le ht.1
      exact div_pos hx (by positivity)
  have hd : Continuous (fun t : ℝ => (m:ℂ)^(1/2+a+t*I)*(k:ℂ)^(1/2+b-t*I)) := by
    have hm0 : (m:ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    have hk0 : (k:ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    simp_rw [Complex.cpow_def_of_ne_zero hm0,Complex.cpow_def_of_ne_zero hk0]
    fun_prop
  have hdi := hd.inv₀ (fun t => mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (by omega : m ≠ 0))))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (by omega : k ≠ 0)))))
  unfold directTerm error
  simp only [div_eq_mul_inv]
  exact ((PRZZArithmeticTime.kernel_measurable a b _ hx (by linarith) (by linarith)).aestronglyMeasurable.sub
      (hw.aestronglyMeasurable measurableSet_Icc)).mul hdi.aestronglyMeasurable

theorem rectangles_integral (T : ℝ) (f : ℕ × ℕ → ℝ → ℂ) (w : ℕ × ℕ → ℝ)
    (hw : Summable w) (hw0 : ∀ p, 0 ≤ w p)
    (hm : ∀ p, AEStronglyMeasurable (f p) (volume.restrict (Icc T (2*T))))
    (hb : ∀ p t, t ∈ Icc T (2*T) → ‖f p t‖ ≤ w p) :
    Tendsto (fun L : ℕ => ∫ t in Icc T (2*T),
      ∑ p ∈ Finset.range L ×ˢ Finset.range L, f p t) atTop
      (𝓝 (∫ t in Icc T (2*T), ∑' p, f p t)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => ∑' p, w p)
  · intro L
    have hh := Finset.aestronglyMeasurable_sum
      (Finset.range L ×ˢ Finset.range L) (fun p _ => hm p)
    have he : (∑ p ∈ Finset.range L ×ˢ Finset.range L, f p) =
        (fun t => ∑ p ∈ Finset.range L ×ˢ Finset.range L, f p t) := by
      funext t
      simp only [Finset.sum_apply]
    rw [he] at hh
    exact hh
  · exact continuousOn_const.integrableOn_compact isCompact_Icc
  · intro L
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun p _ => hb p t ht)).trans
      (hw.sum_le_tsum _ (fun p _ => hw0 p)))
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hn := hw.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => hb p t ht)
    exact hn.of_norm.hasSum.comp PRZZL1Truncation.rectangles_tendsto

theorem weighted_cutoff_removed (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hab : a+b ≠ 0) (T : ℝ) (hT : 256*Real.pi ≤ T) (hT' : 128 ≤ T)
    (phi : ℝ → ℂ) (hphi : Continuous phi) :
    Tendsto (fun L : ℕ => ∫ t in Icc T (2*T), phi t *
      directSum L a b (fun n t => error a b n t) t) atTop
      (𝓝 (∫ t in Icc T (2*T), phi t * ∑' p : ℕ × ℕ,
        directTerm a b (fun n t => error a b n t) t (p.1+1) (p.2+1))) := by
  obtain ⟨C,hC,h⟩ := PRZZProductSummation.arithmetic_bound
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hphi.continuousOn
  let E := max D 0
  let B := E*(C*(1+32/‖a+b‖^2)*T^((1/8:ℝ)-1/4))
  let w := fun p : ℕ × ℕ => B*(((p.1:ℝ)+1)^(-1-(1/8:ℝ))*((p.2:ℝ)+1)^(-1-(1/8:ℝ)))
  have hn : Summable (fun n : ℕ => ((n:ℝ)+1)^(-1-(1/8:ℝ))) := by
    have hh := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr
      (by norm_num : -1-(1/8:ℝ) < -1))
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  have hw : Summable w := (hn.mul_of_nonneg hn (by intro n; positivity)
    (by intro n; positivity)).mul_left B
  have har := (abs_le.mp ((Complex.abs_re_le_norm a).trans ha)).1
  have hbr := (abs_le.mp ((Complex.abs_re_le_norm b).trans hb)).1
  have hbnd (p : ℕ × ℕ) (t : ℝ) (ht : t ∈ Icc T (2*T)) :
      ‖phi t * directTerm a b (fun n t => error a b n t) t (p.1+1) (p.2+1)‖ ≤ w p := by
    rw [norm_mul]
    have hh := h a b ha hb hab T t (1/4) (1/8) hT hT' ht.1 ht.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) (p.1+1) (p.2+1) (by omega) (by omega)
    have hp := mul_le_mul ((hD t ht).trans (le_max_left D 0)) hh
      (norm_nonneg _) (le_max_right D 0)
    simpa only [w,B,E,Nat.cast_add,Nat.cast_one,mul_assoc] using hp
  have hh := rectangles_integral T
    (fun p t => phi t * directTerm a b (fun n t => error a b n t) t (p.1+1) (p.2+1)) w hw
    (by intro p; dsimp [w,B,E]; positivity)
    (fun p => hphi.aestronglyMeasurable.mul
      (term_measurable a b ha hb hab T (by linarith) _ _ (by omega) (by omega))) hbnd
  simpa only [directSum,PRZZL1Truncation.positive_sum,Finset.sum_product,
    Finset.mul_sum,tsum_mul_left] using hh

theorem mollified_cutoff_removed (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hab : a+b ≠ 0) (T : ℝ) (hT : 256*Real.pi ≤ T) (hT' : 128 ≤ T)
    (phi : ℝ → ℂ) (hphi : Continuous phi) (c e : ℕ → ℂ) (N : ℕ) :
    Tendsto (fun L : ℕ => ∫ t in Icc T (2*T),
      PRZZMollifiedTime.mollifierWeight phi c e N t *
      directSum L a b (fun n t => error a b n t) t) atTop
      (𝓝 (∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi c e N t *
        ∑' p : ℕ × ℕ, directTerm a b (fun n t => error a b n t) t (p.1+1) (p.2+1))) :=
  weighted_cutoff_removed a b ha hb hab T hT hT' _
    (PRZZMollifiedTime.mollifierWeight_continuous phi hphi c e N)

/-- Actual convolution coefficients, with the square-root denominators
retained. The N log^(2 degree) cost is supplied, not assumed. -/
theorem source_bound (s eps : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1/2)
    (he : 0 < eps) (he' : eps ≤ 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 →
    s ≤ 1/2+a.re → s ≤ 1/2+b.re → ∀ T : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → ∀ js : List ℕ, ∀ N : ℕ, 1 ≤ N →
    ∀ phi : ℝ → ℂ, Continuous phi →
    ‖∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N t *
      ∑' p : ℕ × ℕ, directTerm a b (fun n t => error a b n t) t (p.1+1) (p.2+1)‖ ≤
      (C*(1+32/‖a+b‖^2)*T^(eps-s)) *
        (4*(N:ℝ)*(Real.log N)^(2*PRZZGCoefficient.degree js)) *
        (∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,hC,h⟩ := PRZZProductSummation.integrated_bound s eps hs hs' he he'
  refine ⟨C,hC,?_⟩
  intro a b ha hb hab hsa hsb T hT hT' js N hN phi hphi
  have hh := h a b ha hb hab hsa hsb T hT hT' _
    (PRZZMollifiedTime.mollifierWeight_continuous phi hphi
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N)
  apply hh.trans
  have hi : (∫ t in Icc T (2*T), ‖PRZZMollifiedTime.mollifierWeight phi
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N t‖) ≤
      (4*(N:ℝ)*(Real.log N)^(2*PRZZGCoefficient.degree js)) *
      (∫ t in Icc T (2*T), ‖phi t‖) := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _))
      ((hphi.norm.const_mul _).integrableOn_Icc)
    exact Filter.Eventually.of_forall (PRZZReplacementMass.source_weight_bound js N hN phi)
  exact (mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq (by ring)

/-- Absorb the actual coefficient logarithms using an explicitly reserved
margin. This is the replacement-error budget, not the entire PRZZ error. -/
theorem source_absorbed (js : List ℕ) (s eps delta : ℝ)
    (hs : 0 ≤ s) (hs' : s ≤ 1/2) (he : 0 < eps) (he' : eps ≤ 1/2)
    (hmargin : eps-s < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 →
    s ≤ 1/2+a.re → s ≤ 1/2+b.re → ∀ T : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ T →
    ∀ phi : ℝ → ℂ, Continuous phi →
    ‖∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N t *
      ∑' p : ℕ × ℕ, directTerm a b (fun n t => error a b n t) t (p.1+1) (p.2+1)‖ ≤
      C*(1+32/‖a+b‖^2)*(N:ℝ)*T^delta*(∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,hC,h⟩ := source_bound s eps hs hs' he he'
  obtain ⟨D,hD,hd⟩ := PRZZOptimalOuter.power_log_absorbed
    (2*PRZZGCoefficient.degree js) (eps-s) delta hmargin
  refine ⟨4*C*D,by positivity,?_⟩
  intro a b ha hb hab hsa hsb T hT hT' N hN hNT phi hphi
  have hlog0 : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hlog : Real.log (N:ℝ) ≤ Real.log T := Real.log_le_log
    (by exact_mod_cast (by omega : 0 < N)) hNT
  have hp : T^(eps-s)*(Real.log N)^(2*PRZZGCoefficient.degree js) ≤ D*T^delta := by
    apply le_trans _ (hd T (by linarith))
    gcongr
  have hi : 0 ≤ ∫ t in Icc T (2*T), ‖phi t‖ := integral_nonneg (fun _ => norm_nonneg _)
  apply (h a b ha hb hab hsa hsb T hT hT' js N hN phi hphi).trans
  have hh := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 4*C*(1+32/‖a+b‖^2)*(N:ℝ)*(∫ t in Icc T (2*T), ‖phi t‖) by positivity)
  convert hh using 1 <;> ring

/-- The correction series is the literal difference of the two convergent
Gamma/main-kernel series, also under the actual weighted time integral. -/
theorem difference_integral (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hab : a+b ≠ 0) (T : ℝ) (hT : 256*Real.pi ≤ T) (hT' : 128 ≤ T)
    (w : ℝ → ℂ) :
    (∫ t in Icc T (2*T), w t * PRZZReplacementIntegral.difference a b t) =
      ∫ t in Icc T (2*T), w t * ∑' p : ℕ × ℕ,
        directTerm a b (fun n t => error a b n t) t (p.1+1) (p.2+1) := by
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only [PRZZReplacementIntegral.difference]
  rw [PRZZActualDirectSum.infinite_replacement a b ha hb hab T t hT hT' ht.1 ht.2]
  rfl

#print axioms difference_integral
#print axioms source_absorbed
#print axioms source_bound
#print axioms term_measurable
#print axioms rectangles_integral
#print axioms weighted_cutoff_removed
#print axioms mollified_cutoff_removed
end XiPrime8845.PRZZProductTime

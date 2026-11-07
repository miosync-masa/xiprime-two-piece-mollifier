import PRZZContourAFE
import PRZZActualDirectSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Identification of the right contour with the actual arithmetic series.
The noncentral pole remainder is retained in the resulting AFE. -/
noncomputable section
open Complex MeasureTheory
open scoped BigOperators
namespace XiPrime8845.PRZZSeriesAFE
open PRZZAFEDual PRZZContourAFE PRZZActualDirectSum PRZZL1Finite
set_option maxHeartbeats 3000000

def term (a b : ℂ) (t : ℝ) (p : ℕ × ℕ) (v : ℝ) : ℂ :=
  PRZZMellinTail.integrand a b 1 t v /
    (((p.1:ℂ)+1)^(leftArg a t+(2+(v:ℂ)*I))*
     ((p.2:ℂ)+1)^(rightArg b t+(2+(v:ℂ)*I)))

theorem shifted_summable (z : ℂ) (hz : 1 < z.re) :
    Summable (fun n : ℕ => 1/((n:ℂ)+1)^z) := by
  simpa only [Nat.cast_add,Nat.cast_one] using
    (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hz)

theorem contour_series (a b : ℂ) (t v : ℝ)
    (ha : -(1/2:ℝ) < a.re) (hb : -(1/2:ℝ) < b.re) :
    PRZZFiniteContour.integrand a b t (2+(v:ℂ)*I) =
      ∑' p : ℕ × ℕ, term a b t p v := by
  have hla : 1 < (leftArg a t+(2+(v:ℂ)*I)).re := by simp [leftArg]; linarith
  have hrb : 1 < (rightArg b t+(2+(v:ℂ)*I)).re := by simp [rightArg]; linarith
  have hl := shifted_summable _ hla
  have hr := shifted_summable _ hrb
  rw [PRZZFiniteContour.integrand,PRZZContourKernel.numerator_eq_actual a b _ t
    (by linarith) (by linarith),zeta_eq_tsum_one_div_nat_add_one_cpow hla,
    zeta_eq_tsum_one_div_nat_add_one_cpow hrb,
    tsum_mul_tsum_of_summable_norm hl.norm hr.norm]
  simp only [term,PRZZMellinTail.integrand,PRZZMellinTail.factor,Complex.ofReal_one,one_cpow]
  rw [← tsum_mul_left,← tsum_div_const]
  apply tsum_congr
  intro p
  ring

/-- Exact kernel identification for each positive arithmetic pair. -/
theorem term_eq (a b : ℂ) (t v : ℝ) (p : ℕ × ℕ) :
    term a b t p v =
      PRZZMellinTail.integrand a b ((p.1+1)*(p.2+1):ℕ) t v /
        (((p.1:ℂ)+1)^leftArg a t*((p.2:ℂ)+1)^rightArg b t) := by
  have hm : (p.1:ℂ)+1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero p.1)
  have hk : (p.2:ℂ)+1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero p.2)
  unfold term PRZZMellinTail.integrand PRZZMellinTail.factor
  rw [Complex.cpow_add _ _ hm,Complex.cpow_add _ _ hk]
  push_cast
  rw [show ((p.1:ℂ)+1)*((p.2:ℂ)+1) =
    (((p.1:ℝ)+1)*((p.2:ℝ)+1):ℝ) by push_cast; rfl,
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  simp only [Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one,one_cpow,cpow_neg]
  ring

theorem term_integral (a b : ℂ) (t : ℝ) (p : ℕ × ℕ) :
    (1/(2*(Real.pi:ℂ)))*(∫ v : ℝ, term a b t p v) =
      directTerm a b (actualWeight a b) t (p.1+1) (p.2+1) := by
  simp_rw [term_eq]
  rw [integral_div]
  unfold directTerm actualWeight
  rw [PRZZMellinTail.kernel_eq]
  simp only [Nat.cast_add,Nat.cast_one,leftArg,rightArg]
  ring

theorem term_bound (a b : ℂ) (t v : ℝ) (p : ℕ × ℕ)
    (ha : -(1/2:ℝ) ≤ a.re) (hb : -(1/2:ℝ) ≤ b.re) :
    ‖term a b t p v‖ ≤ ‖PRZZMellinTail.integrand a b 1 t v‖ *
      (1/((p.1:ℝ)+1)^2)*(1/((p.2:ℝ)+1)^2) := by
  have hl : ((p.1:ℝ)+1)^2 ≤ ‖((p.1:ℂ)+1)^(leftArg a t+(2+(v:ℂ)*I))‖ := by
    rw [show (p.1:ℂ)+1 = (((p.1:ℝ)+1):ℝ) by push_cast; rfl,
      norm_cpow_eq_rpow_re_of_pos (by positivity),← Real.rpow_two]
    apply Real.rpow_le_rpow_of_exponent_le (by have := (Nat.cast_nonneg p.1 : (0:ℝ) ≤ p.1); linarith)
    simp [leftArg]; linarith
  have hr : ((p.2:ℝ)+1)^2 ≤ ‖((p.2:ℂ)+1)^(rightArg b t+(2+(v:ℂ)*I))‖ := by
    rw [show (p.2:ℂ)+1 = (((p.2:ℝ)+1):ℝ) by push_cast; rfl,
      norm_cpow_eq_rpow_re_of_pos (by positivity),← Real.rpow_two]
    apply Real.rpow_le_rpow_of_exponent_le (by have := (Nat.cast_nonneg p.2 : (0:ℝ) ≤ p.2); linarith)
    simp [rightArg]; linarith
  rw [term,norm_div,norm_mul]
  have hd := mul_le_mul hl hr (by positivity) (norm_nonneg _)
  exact (div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hd).trans_eq
    (by simp only [div_eq_mul_inv,mul_inv_rev]; ring)

/-- Joint absolute integrability is supplied, not assumed as an exchange gate. -/
theorem summable_integral_norm (a b : ℂ) (t : ℝ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0) :
    (∀ p, Integrable (term a b t p)) ∧
      Summable (fun p : ℕ × ℕ => ∫ v : ℝ, ‖term a b t p v‖) := by
  have hi := PRZZMellinTail.integrand_integrable a b ha ha' hb hb' hs 1 t (by norm_num)
  have hmaj (p : ℕ × ℕ) := (hi.norm.mul_const (1/((p.1:ℝ)+1)^2)).mul_const
    (1/((p.2:ℝ)+1)^2)
  have hj (p : ℕ × ℕ) : Integrable (term a b t p) := by
    apply (hmaj p).mono'
    · have he : term a b t p = fun v =>
          PRZZMellinTail.integrand a b ((p.1+1)*(p.2+1):ℕ) t v /
            (((p.1:ℂ)+1)^leftArg a t*((p.2:ℂ)+1)^rightArg b t) := funext (fun v => term_eq a b t v p)
      rw [he]
      exact ((PRZZMellinTail.integrand_continuous a b _ t (by positivity) ha hb).div_const _).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun v => term_bound a b t v p ha.le hb.le)
  refine ⟨hj,?_⟩
  have hp : Summable (fun n : ℕ => 1/((n:ℝ)+1)^2) := by
    simpa only [Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  apply ((hp.mul_of_nonneg hp (by intro n; positivity) (by intro n; positivity)).mul_left
    (∫ v : ℝ, ‖PRZZMellinTail.integrand a b 1 t v‖)).of_nonneg_of_le
  · intro p; exact integral_nonneg (fun v => norm_nonneg _)
  · intro p
    have hh := integral_mono (hj p).norm (hmaj p) (fun v => term_bound a b t v p ha.le hb.le)
    simpa only [integral_mul_const,mul_assoc] using hh

theorem positiveIntegral_series (a b : ℂ) (t : ℝ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0) :
    positiveIntegral a b t = ∑' p : ℕ × ℕ,
      directTerm a b (actualWeight a b) t (p.1+1) (p.2+1) := by
  obtain ⟨hi,habs⟩ := summable_integral_norm a b t ha ha' hb hb' hs
  unfold positiveIntegral
  simp_rw [contour_series a b t _ ha hb]
  rw [← integral_tsum_of_summable_integral_norm hi habs,← tsum_mul_left]
  exact tsum_congr (fun p => term_integral a b t p)

theorem series_afe (a b : ℂ) (t : ℝ)
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hs : a+b ≠ 0) (ht : 1 ≤ t) :
    riemannZeta (leftArg a t)*riemannZeta (rightArg b t) =
      (∑' p : ℕ × ℕ, directTerm a b (actualWeight a b) t (p.1+1) (p.2+1)) +
      dualMultiplier a b t *
        (∑' p : ℕ × ℕ, directTerm (-b) (-a) (actualWeight (-b) (-a)) t (p.1+1) (p.2+1)) -
      noncentralSum a b t := by
  have ar := abs_le.mp ((abs_re_le_norm a).trans ha)
  have br := abs_le.mp ((abs_re_le_norm b).trans hb)
  have hs' : -b + -a ≠ 0 := by intro hh; apply hs; linear_combination -hh
  rw [contour_afe a b t ha hb hs ht,
    positiveIntegral_series a b t (by linarith) (by linarith) (by linarith) (by linarith) hs,
    positiveIntegral_series (-b) (-a) t (by simp; linarith) (by simp; linarith)
      (by simp; linarith) (by simp; linarith) hs']

#print axioms term_bound
#print axioms summable_integral_norm
#print axioms positiveIntegral_series
#print axioms series_afe
#print axioms shifted_summable
#print axioms contour_series
#print axioms term_eq
#print axioms term_integral
end XiPrime8845.PRZZSeriesAFE

import PRZZSeriesAFE
import PRZZMollifiedTime

/-! Weighted time integration of the actual series AFE. The noncentral
residue correction is kept. No identification with the post-Poisson A*
weight, nor replacement of the Gamma kernel by sourceW, is asserted. -/
noncomputable section
open Complex MeasureTheory Set
open scoped BigOperators
namespace XiPrime8845.PRZZIntegratedAFE
open PRZZAFEDual PRZZContourAFE PRZZActualDirectSum PRZZL1Finite PRZZMollifiedTime
set_option maxHeartbeats 3000000

def series (a b : ℂ) (t : ℝ) : ℂ :=
  ∑' p : ℕ × ℕ, directTerm a b (actualWeight a b) t (p.1+1) (p.2+1)

theorem weighted_integrable (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0)
    (R : ℝ) (w : ℝ → ℂ) (hw : Continuous w) :
    IntegrableOn (fun t => w t*series a b t) (Icc (-R) R) := by
  obtain ⟨C,hC,h⟩ := PRZZArithmeticTime.kernel_window_bound a b ha ha' hb hb' hs R
  let f := fun p : ℕ × ℕ => C*(1/((p.1:ℝ)+1)^2)*(1/((p.2:ℝ)+1)^2)
  have hp : Summable (fun n : ℕ => 1/((n:ℝ)+1)^2) := by
    simpa only [Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  have hf : Summable f := by
    simpa [f,mul_assoc] using
      ((hp.mul_of_nonneg hp (by intro n; positivity) (by intro n; positivity)).mul_left C)
  have hbnd (t : ℝ) (ht : t ∈ Icc (-R) R) (p : ℕ × ℕ) :
      ‖directTerm a b (actualWeight a b) t (p.1+1) (p.2+1)‖ ≤ f p := by
    rw [directTerm,norm_div]
    apply (div_le_self (norm_nonneg _) (denominator_one a b ha.le hb.le t _ _
      (by omega) (by omega))).trans
    apply (h _ (by positivity) t (abs_le.mpr ht)).trans_eq
    rw [Real.rpow_neg (by positivity),Real.rpow_two]
    dsimp [f]
    push_cast
    field_simp
  have hm (p : ℕ × ℕ) : StronglyMeasurable
      (fun t => directTerm a b (actualWeight a b) t (p.1+1) (p.2+1)) := by
    unfold directTerm actualWeight
    apply StronglyMeasurable.div
    · exact PRZZArithmeticTime.kernel_measurable a b _ (by positivity) ha hb
    · apply Continuous.stronglyMeasurable
      have hm0 : ((p.1+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p.1
      have hk0 : ((p.2+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p.2
      simp_rw [Complex.cpow_def_of_ne_zero hm0,Complex.cpow_def_of_ne_zero hk0]
      fun_prop
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hw.continuousOn
  have hc : IntegrableOn (fun _ : ℝ => max D 0*(∑' p, f p)) (Icc (-R) R) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  apply hc.mono'
  · exact (hw.stronglyMeasurable.mul (StronglyMeasurable.tsum hm)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [norm_mul]
    apply mul_le_mul ((hD t ht).trans (le_max_left _ _)) _ (norm_nonneg _) (le_max_right _ _)
    exact (norm_tsum_le_tsum_norm (hf.of_nonneg_of_le (fun p => norm_nonneg _) (hbnd t ht))).trans
      ((hf.of_nonneg_of_le (fun p => norm_nonneg _) (hbnd t ht)).tsum_le_tsum (hbnd t ht) hf)

/-- On a compact time window, a continuous cutoff supported in t >= 1
times both literal finite mollifiers.
The two arithmetic sums are outside the time integral; the pole remainder
is kept together with the zeta product on the left. -/
theorem mollified_afe (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : a+b ≠ 0) (R : ℝ) (φ : ℝ → ℂ) (hφ : Continuous φ)
    (hsφ : Function.support φ ⊆ Ici (1:ℝ)) (c e : ℕ → ℂ) (N : ℕ) :
    (∫ t in Icc (-R) R, mollifierWeight φ c e N t *
      (riemannZeta (leftArg a t)*riemannZeta (rightArg b t)+noncentralSum a b t)) =
      (∑' p : ℕ × ℕ, ∫ t in Icc (-R) R, mollifierWeight φ c e N t *
        directTerm a b (actualWeight a b) t (p.1+1) (p.2+1)) +
      (∑' p : ℕ × ℕ, ∫ t in Icc (-R) R,
        (mollifierWeight φ c e N t*dualMultiplier a b t)*
          directTerm (-b) (-a) (actualWeight (-b) (-a)) t (p.1+1) (p.2+1)) := by
  have ar := abs_le.mp ((abs_re_le_norm a).trans ha)
  have br := abs_le.mp ((abs_re_le_norm b).trans hb)
  have ha0 : -(1/2:ℝ) < a.re := by linarith
  have hb0 : -(1/2:ℝ) < b.re := by linarith
  have ha1 : a.re < 1/2 := by linarith
  have hb1 : b.re < 1/2 := by linarith
  have hs' : -b + -a ≠ 0 := by intro hh; apply hs; linear_combination -hh
  let w := mollifierWeight φ c e N
  have hw : Continuous w := mollifierWeight_continuous φ hφ c e N
  have hi := weighted_integrable a b ha0 (by linarith) hb0 (by linarith) hs R w hw
  have hj := weighted_integrable (-b) (-a) (by simp; linarith) (by simp; linarith)
    (by simp; linarith) (by simp; linarith) hs' R
    (fun t => w t*dualMultiplier a b t) (hw.mul (dualMultiplier_continuous a b ha0 ha1 hb0 hb1))
  have he (t : ℝ) : w t*(riemannZeta (leftArg a t)*riemannZeta (rightArg b t)+noncentralSum a b t) =
      w t*series a b t+(w t*dualMultiplier a b t)*series (-b) (-a) t := by
    by_cases ht : φ t = 0
    · simp [w,mollifierWeight,ht]
    · have h := PRZZSeriesAFE.series_afe a b t ha hb hs (hsφ ht)
      change _ = series a b t+dualMultiplier a b t*series (-b) (-a) t-_ at h
      rw [h]; ring
  change (∫ t in Icc (-R) R, w t*_) = _
  simp_rw [he]
  rw [integral_add hi hj,direct_mollified_swap a b ha0 (by linarith) hb0 (by linarith) hs R φ hφ c e N,
    dual_mollified_swap a b ha0 ha1 hb0 hb1 hs R φ hφ c e N]
  congr 1 <;> apply integral_congr_ae <;> apply Filter.Eventually.of_forall <;> intro t <;>
    simp only [series,w,tsum_mul_left]

#print axioms weighted_integrable
#print axioms mollified_afe
end XiPrime8845.PRZZIntegratedAFE

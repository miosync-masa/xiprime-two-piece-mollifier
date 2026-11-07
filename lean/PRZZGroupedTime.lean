import PRZZAFEProgression
import PRZZMollifiedTime

/-! Smooth spatial partition inserted into the literal finite AFE fibres.
The seed plateau and finite scale coverage are explicit. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Filter Topology MeasureTheory Set Complex
namespace XiPrime8845.PRZZGroupedTime
open PRZZAFEIndices PRZZAFEProgression PRZZL1Finite PRZZActualDirectSum
open PRZZArithmeticTime PRZZKernelTime PRZZMellinTail PRZZMollifiedTime
set_option maxHeartbeats 3000000

theorem partition_grouped (L N K : ℕ) (F : ℝ → ℂ) (M : ℝ)
    (hM : 0 < M) (hM1 : M ≤ 1) (hcover : (L:ℝ) ≤ (2:ℝ)^K*M/2)
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (f : PRZZAFEIndices.Index → ℂ) :
    (∑ z ∈ labels L N, ∑ i ∈ fibre L N z, f i) =
      ∑ j ∈ range K, ∑ z ∈ labels L N, ∑ i ∈ fibre L N z,
        piece F ((2:ℝ)^j*M) i.1.1 * f i := by
  have he : ∀ z ∈ labels L N, ∀ i ∈ fibre L N z,
      (∑ j ∈ range K, piece F ((2:ℝ)^j*M) i.1.1) = 1 := by
    intro z hz i hi
    have hm := (mem_product.mp (mem_product.mp (mem_filter.mp hi).1).1).1
    exact piece_sum_one F M i.1.1 K hM hlo hhi
      (hM1.trans (by exact_mod_cast (mem_Icc.mp hm).1))
      ((by exact_mod_cast (mem_Icc.mp hm).2 : (i.1.1:ℝ) ≤ L).trans hcover)
  calc
    _ = ∑ z ∈ labels L N, ∑ i ∈ fibre L N z,
        ∑ j ∈ range K, piece F ((2:ℝ)^j*M) i.1.1*f i := by
      apply sum_congr rfl; intro z hz
      apply sum_congr rfl; intro i hi
      rw [← sum_mul,he z hz i hi,one_mul]
    _ = ∑ z ∈ labels L N, ∑ j ∈ range K, ∑ i ∈ fibre L N z,
        piece F ((2:ℝ)^j*M) i.1.1*f i := by
      apply sum_congr rfl; intro z hz
      rw [sum_comm]
    _ = _ := by rw [sum_comm]

#print axioms partition_grouped
/-- Absolute integral summability supplied by the actual Gamma kernel.
The interval is fixed; this statement does not assert polynomial growth in R. -/
theorem weighted_integrable_series (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0) (R : ℝ)
    (φ : ℝ → ℂ) (hφ : Continuous φ) :
    (∀ p : ℕ × ℕ, IntegrableOn
      (fun t => φ t * directTerm a b (actualWeight a b) t (p.1+1) (p.2+1))
      (Icc (-R) R)) ∧
    Summable (fun p : ℕ × ℕ => ∫ t in Icc (-R) R,
      ‖φ t * directTerm a b (actualWeight a b) t (p.1+1) (p.2+1)‖) := by
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ.continuousOn
  let E := max D 0
  have hE : 0 ≤ E := le_max_right _ _
  obtain ⟨C,hC,h⟩ := kernel_window_bound a b ha ha' hb hb' hs R
  let w := fun p : ℕ × ℕ => C*(1/((p.1:ℝ)+1)^2)*(1/((p.2:ℝ)+1)^2)
  have hw (p : ℕ × ℕ) : 0 ≤ w p := by dsimp [w]; positivity
  have hp : Summable (fun n : ℕ => 1/((n:ℝ)+1)^2) := by
    have hh := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  have hws : Summable w := by
    simpa [w,mul_assoc] using
      ((hp.mul_of_nonneg hp (by intro n; positivity) (by intro n; positivity)).mul_left C)
  have hbound (p : ℕ × ℕ) (t : ℝ) (ht : t ∈ Icc (-R) R) :
      ‖directTerm a b (actualWeight a b) t (p.1+1) (p.2+1)‖ ≤ w p := by
    have hd := denominator_one a b ha.le hb.le t (p.1+1) (p.2+1) (by omega) (by omega)
    rw [directTerm,norm_div]
    apply (div_le_self (norm_nonneg _) hd).trans
    apply (h _ (by positivity) t (abs_le.mpr ht)).trans_eq
    rw [Real.rpow_neg (by positivity),Real.rpow_two]
    dsimp [w]
    push_cast
    field_simp
  have hweighted (p : ℕ × ℕ) (t : ℝ) (ht : t ∈ Icc (-R) R) :
      ‖φ t * directTerm a b (actualWeight a b) t (p.1+1) (p.2+1)‖ ≤ E*w p := by
    rw [norm_mul]
    exact mul_le_mul ((hD t ht).trans (le_max_left _ _)) (hbound p t ht)
      (norm_nonneg _) hE
  have hconst (p : ℕ × ℕ) : IntegrableOn (fun _ : ℝ => E*w p) (Icc (-R) R) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hi (p : ℕ × ℕ) : IntegrableOn
      (fun t => φ t * directTerm a b (actualWeight a b) t (p.1+1) (p.2+1)) (Icc (-R) R) := by
    apply (hconst p).mono'
    · apply StronglyMeasurable.aestronglyMeasurable
      apply hφ.stronglyMeasurable.mul
      unfold directTerm actualWeight
      apply StronglyMeasurable.div
      · exact kernel_measurable a b _ (by positivity) ha hb
      · apply Continuous.stronglyMeasurable
        have hm : ((p.1+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero p.1)
        have hk : ((p.2+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero p.2)
        simp_rw [Complex.cpow_def_of_ne_zero hm,Complex.cpow_def_of_ne_zero hk]
        fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hweighted p t ht
  refine ⟨hi,?_⟩
  apply ((hws.mul_left E).mul_right (volume (Icc (-R) R)).toReal).of_nonneg_of_le
  · intro p; exact integral_nonneg (fun t => norm_nonneg _)
  · intro p
    have hh := setIntegral_mono_on (hi p).norm (hconst p)
      measurableSet_Icc (hweighted p)
    simpa only [setIntegral_const,smul_eq_mul,Measure.real,mul_comm] using hh

#print axioms weighted_integrable_series

/-- Rectangular arithmetic cutoffs are removed under the weighted time
integral, using supplied absolute integral summability of the actual kernel. -/
theorem weighted_cutoff_removed (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0) (R : ℝ)
    (φ : ℝ → ℂ) (hφ : Continuous φ) :
    Tendsto (fun L : ℕ => ∫ t in Icc (-R) R,
      φ t * directSum L a b (actualWeight a b) t) atTop
      (𝓝 (∫ t in Icc (-R) R, ∑' p : ℕ × ℕ,
        φ t * directTerm a b (actualWeight a b) t (p.1+1) (p.2+1))) := by
  obtain ⟨hi,hsum⟩ := weighted_integrable_series a b ha ha' hb hb' hs R φ hφ
  have hj : Summable (fun p : ℕ × ℕ => ∫ t in Icc (-R) R,
      φ t * directTerm a b (actualWeight a b) t (p.1+1) (p.2+1)) := by
    apply Summable.of_norm
    exact hsum.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => norm_integral_le_integral_norm _)
  have hh := hj.hasSum.comp PRZZL1Truncation.rectangles_tendsto
  rw [weighted_time_swap a b ha ha' hb hb' hs R φ hφ] at hh
  have he (L : ℕ) :
      (∫ t in Icc (-R) R, φ t * directSum L a b (actualWeight a b) t) =
      ∑ p ∈ (range L) ×ˢ (range L), ∫ t in Icc (-R) R,
        φ t * directTerm a b (actualWeight a b) t (p.1+1) (p.2+1) := by
    rw [← integral_finsetSum _ (fun p hp => hi p)]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [directSum,PRZZL1Truncation.positive_sum,sum_product,mul_sum]
  simpa only [he,Function.comp_def] using hh

#print axioms weighted_cutoff_removed
/-- The original labelled four-index sum, including both mollifiers,
converges under a continuous weighted time integral. -/
theorem grouped_time_cutoff_removed (N : ℕ) (c e : ℕ → ℂ) (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0) (R : ℝ)
    (φ : ℝ → ℂ) (hφ : Continuous φ) :
    Tendsto (fun L : ℕ => ∫ t in Icc (-R) R,
      φ t * (∑ z ∈ labels L N, ∑ i ∈ fibre L N z,
        term c e a b (actualWeight a b) t i.1.1 i.1.2 i.2.1 i.2.2)) atTop
      (𝓝 (∫ t in Icc (-R) R, ∑' p : ℕ × ℕ,
        mollifierWeight φ c e N t *
          directTerm a b (actualWeight a b) t (p.1+1) (p.2+1))) := by
  have hh := weighted_cutoff_removed a b ha ha' hb hb' hs R
    (mollifierWeight φ c e N) (mollifierWeight_continuous φ hφ c e N)
  have he (L : ℕ) (t : ℝ) :
      φ t * (∑ z ∈ labels L N, ∑ i ∈ fibre L N z,
        term c e a b (actualWeight a b) t i.1.1 i.1.2 i.2.1 i.2.2) =
      mollifierWeight φ c e N t * directSum L a b (actualWeight a b) t := by
    rw [← direct_grouped]
    unfold mollifierWeight
    ring
  simpa only [he] using hh

#print axioms grouped_time_cutoff_removed
/-- The number of spatial pieces grows with L to preserve exact coverage.
No fixed finite partition is silently used when removing the cutoff. -/
theorem partitioned_time_cutoff_removed (N : ℕ) (c e : ℕ → ℂ) (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0) (R : ℝ)
    (φ : ℝ → ℂ) (hφ : Continuous φ) (F : ℝ → ℂ) (M : ℝ) (K : ℕ → ℕ)
    (hM : 0 < M) (hM1 : M ≤ 1) (hcover : ∀ L : ℕ, (L:ℝ) ≤ (2:ℝ)^(K L)*M/2)
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0) :
    Tendsto (fun L : ℕ => ∫ t in Icc (-R) R,
      φ t * (∑ j ∈ range (K L), ∑ z ∈ labels L N, ∑ i ∈ fibre L N z,
        piece F ((2:ℝ)^j*M) i.1.1 *
          term c e a b (actualWeight a b) t i.1.1 i.1.2 i.2.1 i.2.2)) atTop
      (𝓝 (∫ t in Icc (-R) R, ∑' p : ℕ × ℕ,
        mollifierWeight φ c e N t *
          directTerm a b (actualWeight a b) t (p.1+1) (p.2+1))) := by
  simp_rw [← partition_grouped _ N _ F M hM hM1 (hcover _) hlo hhi]
  exact grouped_time_cutoff_removed N c e a b ha ha' hb hb' hs R φ hφ

#print axioms partitioned_time_cutoff_removed
/-- Every actual fibre supplies the signed congruence, the eliminated k,
and its original truncation bounds. -/
theorem fibre_quotient (L N : ℕ) (z : Label) (i : PRZZAFEIndices.Index)
    (hi : i ∈ fibre L N z) :
    let d := Nat.gcd i.2.1 i.2.2
    let u : ℤ := (i.2.1/d : ℕ)
    let v : ℤ := (i.2.2/d : ℕ)
    v ∣ (i.1.1:ℤ)*u-z.2.1 ∧
      (i.1.2:ℤ) = ((i.1.1:ℤ)*u-z.2.1)/v ∧
      1 ≤ ((i.1.1:ℤ)*u-z.2.1)/v ∧ ((i.1.1:ℤ)*u-z.2.1)/v ≤ L := by
  dsimp only
  have hm := mem_filter.mp hi
  have hr := (mem_product.mp (mem_product.mp hm.1).2).2
  have hk := (mem_product.mp (mem_product.mp hm.1).1).2
  have hr0 : 0 < i.2.2 := (mem_Icc.mp hr).1
  have hd : 0 < Nat.gcd i.2.1 i.2.2 := Nat.gcd_pos_of_pos_right i.2.1 hr0
  have hv : (i.2.2/Nat.gcd i.2.1 i.2.2 : ℕ) ≠ 0 := by
    exact Nat.ne_of_gt (Nat.div_pos
      (Nat.le_of_dvd hr0 (Nat.gcd_dvd_right i.2.1 i.2.2)) hd)
  have he := congrArg (fun z : Label => z.2.1) hm.2
  change (i.1.1:ℤ)*(i.2.1/Nat.gcd i.2.1 i.2.2:ℕ)-
    (i.1.2:ℤ)*(i.2.2/Nat.gcd i.2.1 i.2.2:ℕ) = z.2.1 at he
  obtain ⟨hc,hq⟩ := (quotient_iff _ _ _ _ _ (by exact_mod_cast hv)).mp he
  exact ⟨hc,hq,by rw [← hq]; exact_mod_cast (mem_Icc.mp hk).1,
    by rw [← hq]; exact_mod_cast (mem_Icc.mp hk).2⟩

#print axioms fibre_quotient
end XiPrime8845.PRZZGroupedTime

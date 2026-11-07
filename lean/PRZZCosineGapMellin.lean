import PRZZCosineMellin
import PRZZZeroReflection

/-! Absolute summation of the evaluated positive-gap cosine Mellin
kernel, including the factor two for signed gaps. This proves the zeta
factor and reflected diagonal kernel; it does not identify this evaluated
kernel with the actual uncut spatial integral. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZCosineGapMellin
open PRZZCosineMellinCore PRZZCosineMellin
set_option maxHeartbeats 5000000

def term (sigma : ℂ) (X : ℝ) (n : ℕ) (tau : ℝ) : ℂ :=
  evaluated sigma X tau/((n+1:ℕ):ℂ)^(exponent sigma tau)

theorem exponent_re (sigma : ℂ) (hn : ‖sigma‖ ≤ 1/8) (tau : ℝ) :
    2 ≤ (exponent sigma tau).re := by
  have hh := abs_le.mp ((Complex.abs_re_le_norm sigma).trans hn)
  dsimp [exponent,line]
  simp only [add_re,mul_re,ofReal_re,ofReal_im,I_re,I_im,mul_zero,mul_one,sub_zero]
  norm_num
  linarith [hh.1]

theorem term_bound (sigma : ℂ) (hn : ‖sigma‖ ≤ 1/8) (X tau : ℝ) (n : ℕ) :
    ‖term sigma X n tau‖ ≤ ‖evaluated sigma X tau‖*(1/((n+1:ℕ):ℝ)^2) := by
  have hd : ((n+1:ℕ):ℝ)^2 ≤ ‖((n+1:ℕ):ℂ)^(exponent sigma tau)‖ := by
    rw [← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
      ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (Nat.le_add_left 1 n))
      (exponent_re sigma hn tau)
  rw [term,norm_div]
  exact (div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hd).trans_eq (by ring)

theorem absolute_exchange (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) :
    (∀ n, Integrable (term sigma X n)) ∧
      Summable (fun n : ℕ => ∫ tau : ℝ, ‖term sigma X n tau‖) := by
  have hi := evaluated_integrable sigma hs hn X hX
  have hj (n : ℕ) : Integrable (term sigma X n) := by
    have hd : Continuous (fun tau : ℝ => ((n+1:ℕ):ℂ)^(exponent sigma tau)) := by
      have hnC : ((n+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
      simp_rw [Complex.cpow_def_of_ne_zero hnC]
      dsimp [exponent,line]
      fun_prop
    apply (hi.norm.mul_const (1/((n+1:ℕ):ℝ)^2)).mono'
    · exact hi.aestronglyMeasurable.div₀ hd.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun tau => term_bound sigma hn X tau n)
  refine ⟨hj,?_⟩
  have hp : Summable (fun n : ℕ => 1/((n+1:ℕ):ℝ)^2) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  apply (hp.mul_left (∫ tau : ℝ, ‖evaluated sigma X tau‖)).of_nonneg_of_le
  · intro n; exact integral_nonneg (fun tau => norm_nonneg _)
  · intro n
    have hh := integral_mono (hj n).norm (hi.norm.mul_const (1/((n+1:ℕ):ℝ)^2))
      (fun tau => term_bound sigma hn X tau n)
    simpa only [integral_mul_const] using hh

theorem zeta_expansion (sigma : ℂ) (hn : ‖sigma‖ ≤ 1/8) (X tau : ℝ) :
    (∑' n : ℕ, term sigma X n tau) =
      riemannZeta (exponent sigma tau)*evaluated sigma X tau := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by linarith [exponent_re sigma hn tau]),← tsum_mul_right]
  apply tsum_congr
  intro n
  simp only [term,Nat.cast_add,Nat.cast_one]
  ring

theorem gap_integral (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) :
    (∑' n : ℕ, ∫ tau : ℝ, term sigma X n tau) =
      ∫ tau : ℝ, riemannZeta (exponent sigma tau)*evaluated sigma X tau := by
  obtain ⟨hi,ha⟩ := absolute_exchange sigma hs hn X hX
  rw [integral_tsum_of_summable_integral_norm hi ha]
  simp_rw [zeta_expansion sigma hn]

theorem signed_kernel (sigma : ℂ) (P t tau : ℝ) :
    2*(riemannZeta (exponent sigma tau)*evaluated sigma (2*Real.pi*t/P) tau) =
      PRZZZeroReflection.cosineKernel sigma P t (line tau) := by
  unfold PRZZZeroReflection.cosineKernel evaluated coefficient limitMoment exponent
  ring

/-- The evaluated gap cutoff is removed by absolute-integral
summability, before performing the reflection. -/
theorem gap_partial_limit (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) :
    Tendsto (fun L : ℕ => ∑ n ∈ Finset.range L, ∫ tau : ℝ, term sigma X n tau) atTop
      (𝓝 (∫ tau : ℝ, riemannZeta (exponent sigma tau)*evaluated sigma X tau)) := by
  obtain ⟨hi,ha⟩ := absolute_exchange sigma hs hn X hX
  have hh := (hasSum_integral_of_summable_integral_norm hi ha).tendsto_sum_nat
  simpa only [zeta_expansion sigma hn] using hh

theorem reflected_gap_integral (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (P t : ℝ) (hP : 0 < P) (ht : 0 < t) :
    (t:ℂ)^(-sigma)*(1/(2*Real.pi):ℂ)*
      (2*∑' n : ℕ, ∫ tau : ℝ, term sigma (2*Real.pi*t/P) n tau) =
      ((t/(2*Real.pi):ℝ):ℂ)^(-sigma)*(1/(2*Real.pi):ℂ)*
        ∫ tau : ℝ, PRZZDiagonalMellin.integrand (-sigma) (t/(2*Real.pi*P)) (-line tau) := by
  rw [gap_integral sigma hs hn _ (by positivity)]
  have he (tau : ℝ) : (t:ℂ)^(-sigma)*
      (2*(riemannZeta (exponent sigma tau)*evaluated sigma (2*Real.pi*t/P) tau)) =
      ((t/(2*Real.pi):ℝ):ℂ)^(-sigma)*
        PRZZDiagonalMellin.integrand (-sigma) (t/(2*Real.pi*P)) (-line tau) := by
    rw [signed_kernel]
    apply PRZZZeroReflection.reflected_kernel sigma _ P t hP ht
    · change 0 < (exponent sigma tau).re
      linarith [exponent_re sigma hn tau]
    · intro hh
      have h := exponent_re sigma hn tau
      change 2 ≤ (2*line tau+sigma).re at h
      rw [hh] at h
      norm_num at h
  calc
    _ = (1/(2*Real.pi):ℂ)*∫ tau : ℝ, (t:ℂ)^(-sigma)*
        (2*(riemannZeta (exponent sigma tau)*evaluated sigma (2*Real.pi*t/P) tau)) := by
      simp only [integral_const_mul]; ring
    _ = _ := by simp_rw [he]; rw [integral_const_mul]; ring

/-- The finite signed-gap Mellin sums converge to the actual opposite
diagonal integrand on Re s=-5/4. Moving that line to -1/8 and identifying
the original improper spatial transform remain separate steps. -/
theorem reflected_partial_limit (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (P t : ℝ) (hP : 0 < P) (ht : 0 < t) :
    Tendsto (fun L : ℕ => (t:ℂ)^(-sigma)*(1/(2*Real.pi):ℂ)*
      (2*∑ n ∈ Finset.range L, ∫ tau : ℝ, term sigma (2*Real.pi*t/P) n tau)) atTop
      (𝓝 (((t/(2*Real.pi):ℝ):ℂ)^(-sigma)*(1/(2*Real.pi):ℂ)*
        ∫ tau : ℝ, PRZZDiagonalMellin.integrand (-sigma) (t/(2*Real.pi*P)) (-line tau))) := by
  have h := (gap_partial_limit sigma hs hn (2*Real.pi*t/P) (by positivity)).const_mul
    ((t:ℂ)^(-sigma)*(1/(2*Real.pi):ℂ)*2)
  have he := reflected_gap_integral sigma hs hn P t hP ht
  rw [gap_integral sigma hs hn _ (by positivity)] at he
  have hlim : (t:ℂ)^(-sigma)*(1/(2*Real.pi):ℂ)*2*
      (∫ tau : ℝ, riemannZeta (exponent sigma tau)*evaluated sigma (2*Real.pi*t/P) tau) =
      ((t/(2*Real.pi):ℝ):ℂ)^(-sigma)*(1/(2*Real.pi):ℂ)*
        ∫ tau : ℝ, PRZZDiagonalMellin.integrand (-sigma) (t/(2*Real.pi*P)) (-line tau) := by
    calc
      _ = (t:ℂ)^(-sigma)*(1/(2*Real.pi):ℂ)*
          (2*∫ tau : ℝ, riemannZeta (exponent sigma tau)*evaluated sigma (2*Real.pi*t/P) tau) := by ring
      _ = _ := he
  rw [hlim] at h
  exact h.congr' (Filter.Eventually.of_forall (fun L => by ring))

#print axioms exponent_re
#print axioms term_bound
#print axioms absolute_exchange
#print axioms zeta_expansion
#print axioms gap_integral
#print axioms signed_kernel
#print axioms gap_partial_limit
#print axioms reflected_gap_integral
#print axioms reflected_partial_limit
end XiPrime8845.PRZZCosineGapMellin

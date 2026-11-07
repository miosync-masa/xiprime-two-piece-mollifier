import PRZZSourceCutoffs
import PRZZPhaseError

/-! Supply the small logarithmic ratio from the literal Delta cutoff and
nonzero smooth support witnesses. All finite coefficient masses are retained;
no arithmetic coefficient growth estimate is postulated as a conclusion. -/
noncomputable section
open scoped BigOperators
namespace XiPrime8845.PRZZCutoffPhase
open PRZZSourceCutoffs

/-- The numerical height threshold is supplied for every fixed eps < 1. -/
theorem height_eventually (eps : ℝ) (heps : eps < 1) :
    ∀ᶠ T : ℝ in Filter.atTop, 0 < T ∧ 8 ≤ T^(1-eps) := by
  exact (Filter.eventually_gt_atTop (0:ℝ)).and
    ((tendsto_rpow_atTop (by linarith : 0 < 1-eps)).eventually
      (Filter.eventually_ge_atTop (8:ℝ)))

theorem ratio_bound (T M Q d eps delta m n : ℝ)
    (hT : 0 < T) (hM : 0 < M) (hQ : 0 < Q) (hd : 0 < d)
    (hm : M/2 ≤ m) (hn : Q/2 ≤ d*n)
    (hdelta : |delta| ≤ deltaCutoff T M Q eps/d) :
    |delta/(m*n)| ≤ 4/T^(1-eps) := by
  have hm0 : 0 < m := by linarith
  have hn0 : 0 < n := by nlinarith
  have hp : 0 < T^(1-eps) := Real.rpow_pos_of_pos hT _
  have hprod : M*Q ≤ 4*d*(m*n) := by nlinarith [mul_le_mul hm hn (by positivity) hm0.le]
  rw [abs_div,abs_of_pos (mul_pos hm0 hn0)]
  apply (div_le_div_of_nonneg_right hdelta (by positivity)).trans
  unfold deltaCutoff
  apply (div_le_iff₀ (mul_pos hm0 hn0)).mpr
  apply (div_le_iff₀ hd).mpr
  apply (div_le_iff₀ hp).mpr
  field_simp
  nlinarith

theorem support_ratio (T M Q d eps delta m n : ℝ) (FM F1 : ℝ → ℂ)
    (hT : 0 < T) (hM : 0 < M) (hQ : 0 < Q) (hd : 0 < d)
    (hsM : Function.support FM ⊆ Set.Icc (M/2) (3*M))
    (hs1 : Function.support F1 ⊆ Set.Icc (Q/2) (3*Q))
    (hfm : FM m ≠ 0) (hf1 : F1 (d*n) ≠ 0)
    (hdelta : |delta| ≤ deltaCutoff T M Q eps/d) :
    |delta/(m*n)| ≤ 4/T^(1-eps) :=
  ratio_bound T M Q d eps delta m n hT hM hQ hd
    (hsM hfm).1 (hs1 hf1).1 hdelta

theorem support_small (T M Q d eps delta m n : ℝ) (FM F1 : ℝ → ℂ)
    (hT : 0 < T) (hM : 0 < M) (hQ : 0 < Q) (hd : 0 < d)
    (hsM : Function.support FM ⊆ Set.Icc (M/2) (3*M))
    (hs1 : Function.support F1 ⊆ Set.Icc (Q/2) (3*Q))
    (hfm : FM m ≠ 0) (hf1 : F1 (d*n) ≠ 0)
    (hdelta : |delta| ≤ deltaCutoff T M Q eps/d) (hheight : 8 ≤ T^(1-eps)) :
    |delta/(m*n)| ≤ 1/2 := by
  apply (support_ratio T M Q d eps delta m n FM F1 hT hM hQ hd hsM hs1 hfm hf1 hdelta).trans
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hT _)).mpr (by linarith)

/-- The retained coefficient mass gains two powers of the source ratio.
The coefficients may already include arithmetic masks and finite cutoffs. -/
theorem mass_bound {ι : Type*} (s : Finset ι) (c : ι → ℂ) (u : ι → ℝ)
    (P : ℝ) (hP : 0 < P) (hu : ∀ i ∈ s, |u i| ≤ 4/P) :
    (∑ i ∈ s, ‖c i‖*(u i)^2) ≤ (16/P^2)*∑ i ∈ s, ‖c i‖ := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hh := sq_le_sq₀ (abs_nonneg (u i)) (by positivity : 0 ≤ 4/P) |>.mpr (hu i hi)
  rw [sq_abs,div_pow] at hh
  norm_num only [show (4:ℝ)^2 = 16 by norm_num] at hh
  exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (by ring)

#print axioms ratio_bound
#print axioms height_eventually
#print axioms support_ratio
#print axioms support_small
#print axioms mass_bound

theorem source_finite_error {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (delta m n : ι → ℝ) (T M Q d eps t : ℝ) (FM F1 : ℝ → ℂ)
    (hT : 0 < T) (hM : 0 < M) (hQ : 0 < Q) (hd : 0 < d)
    (hsM : Function.support FM ⊆ Set.Icc (M/2) (3*M))
    (hs1 : Function.support F1 ⊆ Set.Icc (Q/2) (3*Q))
    (hfm : ∀ i ∈ s, FM (m i) ≠ 0) (hf1 : ∀ i ∈ s, F1 (d*n i) ≠ 0)
    (hdelta : ∀ i ∈ s, |delta i| ≤ deltaCutoff T M Q eps/d)
    (hheight : 8 ≤ T^(1-eps)) (ht : |t| ≤ 2*T) :
    ‖(∑ i ∈ s, c i*Complex.exp (Complex.I*((t*Real.log (1+delta i/(m i*n i)):ℝ):ℂ)))-
      ∑ i ∈ s, c i*Complex.exp (Complex.I*((t*(delta i/(m i*n i)):ℝ):ℂ))‖ ≤
      (64*T/(T^(1-eps))^2)*∑ i ∈ s, ‖c i‖ := by
  let u := fun i => delta i/(m i*n i)
  have hu : ∀ i ∈ s, |u i| ≤ 4/T^(1-eps) := fun i hi =>
    support_ratio T M Q d eps (delta i) (m i) (n i) FM F1 hT hM hQ hd
      hsM hs1 (hfm i hi) (hf1 i hi) (hdelta i hi)
  have hsmall : ∀ i ∈ s, |u i| ≤ 1/2 := fun i hi =>
    support_small T M Q d eps (delta i) (m i) (n i) FM F1 hT hM hQ hd
      hsM hs1 (hfm i hi) (hf1 i hi) (hdelta i hi) hheight
  apply (PRZZPhaseError.finite_error s c u t hsmall).trans
  have hm := mass_bound s c u (T^(1-eps)) (Real.rpow_pos_of_pos hT _) hu
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ) ≤ 2)) hm
    (Finset.sum_nonneg (fun i hi => by positivity)) (by positivity : 0 ≤ 2*(2*T))
  exact hh.trans_eq (by ring)

#print axioms source_finite_error
end XiPrime8845.PRZZCutoffPhase

import ShiftedEndpoint

/-! Uniform finite-head identification for the supported coprime convolution.
The translation of the profile and its exponential factor are retained together. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace XiPrime8845.CoprimeHead
open ShiftWeights WeightDerivatives WeightedMobius ShiftedMobius CoprimeShift ShiftedEndpoint
attribute [local instance] Classical.propDecidable

theorem translated_mainTerm (P : Polynomial ℂ) (A : ℂ) (u θ a : ℝ) :
    Complex.exp (-A*a)*mainTerm (u-a) θ P A = -first A u θ P a := by
  simp only [mainTerm, first, weight]
  ring

theorem translated_mainTerm_bound (P : Polynomial ℂ) (A : ℂ) (u θ a C U : ℝ)
    (hθ : 0 < θ) (hA : ‖A‖ ≤ C) (hu : u ≤ U) (ha : a ∈ Set.Icc 0 u) :
    ‖Complex.exp (-A*a)*mainTerm (u-a) θ P A - mainTerm u θ P A‖ ≤
      secondCap P θ C U * a := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v (_ : v ∈ Set.Icc 0 u) => (first_hasDerivAt A u θ v P).hasDerivWithinAt)
    (fun v hv => second_bound A u θ v C U P hθ hA hu hv)
    (convex_Icc (0 : ℝ) u) (show (0 : ℝ) ∈ Set.Icc 0 u from ⟨le_rfl,ha.1.trans ha.2⟩) ha
  rw [translated_mainTerm, mainTerm, ← first_zero]
  simpa only [neg_sub_neg, norm_sub_rev, sub_zero, Real.norm_eq_abs, abs_of_nonneg ha.1] using h

/-- The scaled, translated summand differs from its unshifted-head main term.
Only the unrestricted Mobius approximation occurs in the first error term. -/
theorem head_term_bound (P : Polynomial ℂ) (A : ℂ) (r : ℕ)
    (L u θ C U eps : ℝ) (hr : 0 < r) (hL : 0 < L) (hθ : 0 < θ)
    (hA : ‖A‖ ≤ C) (hu : u ≤ U) (ha : Real.log r/L ∈ Set.Icc 0 u)
    (herr : ‖scaledSum L (u-Real.log r/L) θ P A - mainTerm (u-Real.log r/L) θ P A‖ ≤ eps) :
    ‖supportFactor r L A * scaledSum L (u-Real.log r/L) θ P A - mainTerm u θ P A / r‖ ≤
      (Real.exp (C*U)*eps + secondCap P θ C U*(Real.log r/L))/(r : ℝ) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have he := exp_weight_bound A (Real.log r/L) C U hA
    (by rw [abs_of_nonneg ha.1]; exact ha.2.trans hu)
  have ht := translated_mainTerm_bound P A u θ (Real.log r/L) C U hθ hA hu ha
  unfold supportFactor
  rw [div_mul_eq_mul_div, ← sub_div, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ hr0.le
  have hid : Complex.exp (-A*(Real.log r/L : ℝ))*scaledSum L (u-Real.log r/L) θ P A - mainTerm u θ P A =
      Complex.exp (-A*(Real.log r/L : ℝ))*(scaledSum L (u-Real.log r/L) θ P A-mainTerm (u-Real.log r/L) θ P A) +
      (Complex.exp (-A*(Real.log r/L : ℝ))*mainTerm (u-Real.log r/L) θ P A-mainTerm u θ P A) := by ring
  rw [hid]
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  exact add_le_add (mul_le_mul he herr (norm_nonneg _) (Real.exp_pos _).le) ht

/-- For each fixed finite head, eps/r holds uniformly in A and u.
No convergence at u=0, and no fixed-g hypothesis, is hidden in the statement. -/
theorem finite_head_eventually (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C u₀ U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hu₀ : 0 < u₀) (hU : 0 < U)
    (Q : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ L : ℝ in atTop, ∀ r ∈ Finset.Icc 1 Q, ∀ A : ℂ, ‖A‖ ≤ C →
      ∀ u ∈ Set.Icc u₀ U,
        ‖supportFactor r L A * scaledSum L (u-Real.log r/L) θ P A - mainTerm u θ P A/r‖ ≤ eps/(r : ℝ) := by
  have hconv := shifted_main_term_uniform P hP θ C (u₀/2) U hθ hC (by positivity) hU
  have hsmall : Tendsto (fun L : ℝ => Real.log (max Q 1)/L) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul (Real.log (max Q 1))
  have hsmall₂ := hsmall.const_mul (secondCap P θ C U)
  simp only [mul_zero] at hsmall₂
  have hd : 0 < eps/(2*Real.exp (C*U)) := by positivity
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hsmall.eventually (gt_mem_nhds (show (0 : ℝ) < u₀/2 by positivity)),
    hsmall₂.eventually (gt_mem_nhds (show (0 : ℝ) < eps/2 by positivity)),
    Metric.tendstoUniformlyOn_iff.mp hconv _ hd] with L hL hcut hsmallL happrox
  intro r hr A hA u hu
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (Finset.mem_Icc.mp hr).1
  have hr0 : 0 < r := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hr).1
  have ha0 : 0 ≤ Real.log r/L := div_nonneg (Real.log_nonneg hr1) hL.le
  have haQ : Real.log r/L ≤ Real.log (max Q 1)/L := by
    apply div_le_div_of_nonneg_right _ hL.le
    apply Real.log_le_log (lt_of_lt_of_le zero_lt_one hr1)
    exact_mod_cast (Finset.mem_Icc.mp hr).2.trans (le_max_left Q 1)
  have hshift : u-Real.log r/L ∈ Set.Icc (u₀/2) U := ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have herr := happrox (A,u-Real.log r/L) ⟨hA,hshift⟩
  rw [dist_comm, dist_eq_norm] at herr
  apply (head_term_bound P A r L u θ C U _ hr0 hL hθ hA hu.2
    ⟨ha0,by linarith [hu.1]⟩ herr.le).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have heq : Real.exp (C*U)*(eps/(2*Real.exp (C*U))) = eps/2 := by field_simp
  rw [heq]
  have hb := mul_le_mul_of_nonneg_left haQ (secondCap_nonneg P θ C U hθ hC hU.le)
  linarith

def headSum (Q g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℂ :=
  ∑ r ∈ (Finset.Icc 1 Q).filter (SmoothMobius.supported g),
    supportFactor r L A * scaledSum L (u-Real.log r/L) θ P A

def headMain (Q g : ℕ) (u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℂ :=
  ∑ r ∈ (Finset.Icc 1 Q).filter (SmoothMobius.supported g), mainTerm u θ P A / r

/-- Uniform in g, since all of its supported heads are subsets of one finite set. -/
theorem finite_head_error (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C u₀ U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hu₀ : 0 < u₀) (hU : 0 < U)
    (Q : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ L : ℝ in atTop, ∀ g : ℕ, ∀ A : ℂ, ‖A‖ ≤ C → ∀ u ∈ Set.Icc u₀ U,
      ‖headSum Q g L u θ P A - headMain Q g u θ P A‖ ≤
        eps * SupportProductTail.supportedSum g (Finset.Icc 1 Q) (fun r => 1/(r : ℝ)) := by
  filter_upwards [finite_head_eventually P hP θ C u₀ U hθ hC hu₀ hU Q eps heps] with L hL
  intro g A hA u hu
  unfold headSum headMain SupportProductTail.supportedSum
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro r hr
  simpa only [mul_one_div] using hL r (Finset.mem_filter.mp hr).1 A hA u hu

/-- A fixed finite head is eventually contained in every actual cutoff. -/
theorem finite_head_in_cutoff (Q : ℕ) (u₀ : ℝ) (hu₀ : 0 < u₀) :
    ∀ᶠ L : ℝ in atTop, ∀ u : ℝ, u₀ ≤ u → Q ≤ ⌊Real.exp (L*u)⌋₊ := by
  have h := Real.tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const hu₀)
  filter_upwards [eventually_gt_atTop (0 : ℝ), h.eventually (eventually_ge_atTop (Q : ℝ))] with L hL hQ
  intro u hu
  exact (Nat.le_floor_iff (Real.exp_pos _).le).mpr
    (hQ.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu hL.le)))

#print axioms finite_head_error
#print axioms finite_head_in_cutoff
#print axioms translated_mainTerm
#print axioms translated_mainTerm_bound
#print axioms head_term_bound
#print axioms finite_head_eventually
end XiPrime8845.CoprimeHead

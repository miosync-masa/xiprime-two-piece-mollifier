import CoprimeShift
import SupportProductTail

/-! Bounds at the cutoff endpoint, not uniform convergence at u=0.
The actual scaled coprime sum is dominated by a supported harmonic mass. -/
noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators
namespace XiPrime8845.ShiftedEndpoint
open WeightedMobius WeightDerivatives ShiftedMobius CoprimeShift
attribute [local instance] Classical.propDecidable

theorem absoluteError_bounded :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t → absoluteError t ≤ K := by
  obtain ⟨T, hT⟩ := Metric.tendsto_atTop.mp absoluteError_tendsto 1 (by norm_num)
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image
    (K := Set.Icc (0 : ℝ) (max T 0)) absoluteError_continuous.continuousOn
  refine ⟨max C 1, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro t ht
  by_cases h : t ≤ max T 0
  · exact (hC ⟨t, ⟨ht,h⟩, rfl⟩).trans (le_max_left _ _)
  · have hh := hT t ((le_max_left T 0).trans (le_of_not_ge h))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (show 0 ≤ absoluteError t from abs_nonneg _)] at hh
    exact hh.le.trans (le_max_right _ _)

def scaledCap (P : Polynomial ℂ) (θ C U K : ℝ) : ℝ :=
  (K+1)*firstCap P θ C U + U*K*secondCap P θ C U

theorem scaledCap_nonneg (P : Polynomial ℂ) (θ C U K : ℝ)
    (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 ≤ U) (hK : 0 ≤ K) :
    0 ≤ scaledCap P θ C U K := by
  unfold scaledCap
  have := firstCap_nonneg P θ C U hθ hC hU
  have := secondCap_nonneg P θ C U hθ hC hU
  positivity

theorem mainTerm_bound (P : Polynomial ℂ) (A : ℂ) (u θ C U : ℝ)
    (hθ : 0 < θ) (hA : ‖A‖ ≤ C) (hu : u ∈ Set.Icc 0 U) :
    ‖mainTerm u θ P A‖ ≤ firstCap P θ C U := by
  rw [mainTerm, ← first_zero, norm_neg]
  exact first_bound A u θ 0 C U P hθ hA hu.2 ⟨le_rfl,hu.1⟩

/-- A single bound valid for every L>0 and all 0<=u<=U, including u=0. -/
theorem scaledSum_bound (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (A : ℂ) (L u θ C U K : ℝ) (hL : 0 < L) (hθ : 0 < θ)
    (hA : ‖A‖ ≤ C) (hu : u ∈ Set.Icc 0 U) (hK : 0 ≤ K)
    (hbound : ∀ t : ℝ, 0 ≤ t → absoluteError t ≤ K) :
    ‖scaledSum L u θ P A‖ ≤ scaledCap P θ C U K := by
  have hC := (norm_nonneg A).trans hA
  have hU := hu.1.trans hu.2
  have h₁ := firstCap_nonneg P θ C U hθ hC hU
  have h₂ := secondCap_nonneg P θ C U hθ hC hU
  have herr := weighted_residual_bound L u (firstCap P θ C U) (secondCap P θ C U)
    hL hu.1 (ShiftWeights.weight A u θ P) (first A u θ P) (second A u θ P)
    (fun v => weight_hasDerivAt A u θ v P)
    (fun v => first_hasDerivAt A u θ v P) (second_continuous A u θ P)
    (by simp [ShiftWeights.weight,hP])
    (first_bound A u θ u C U P hθ hA hu.2 ⟨hu.1,le_rfl⟩)
    (fun v hv => second_bound A u θ v C U P hθ hA hu.2 hv)
  have hi : (∫ v in 0..u, absoluteError (L*v)) ≤ U*K := by
    calc
      _ ≤ ∫ v in 0..u, K := intervalIntegral.integral_mono_on hu.1
        ((absoluteError_continuous.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)
        intervalIntegrable_const (fun v hv => hbound _ (mul_nonneg hL.le hv.1))
      _ = u*K := by simp
      _ ≤ U*K := mul_le_mul_of_nonneg_right hu.2 hK
  have hb := add_le_add (mul_le_mul_of_nonneg_right (hbound (L*u) (mul_nonneg hL.le hu.1)) h₁)
    (mul_le_mul_of_nonneg_right hi h₂)
  have hf := first_bound A u θ 0 C U P hθ hA hu.2 ⟨le_rfl,hu.1⟩
  have hn := norm_sub_le (scaledSum L u θ P A + first A u θ P 0) (first A u θ P 0)
  rw [add_sub_cancel_right] at hn
  change ‖scaledSum L u θ P A + first A u θ P 0‖ ≤ _ at herr
  unfold scaledCap
  linarith [herr.trans hb]

def coprimeCap (P : Polynomial ℂ) (θ C U K : ℝ) : ℝ :=
  Real.exp (C*U)*scaledCap P θ C U K

theorem scaled_coprime_bound (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (A : ℂ) (g : ℕ) (L u θ C U K : ℝ) (hL : 0 < L) (hθ : 0 < θ)
    (hA : ‖A‖ ≤ C) (hu : u ∈ Set.Icc 0 U) (hK : 0 ≤ K)
    (hbound : ∀ t : ℝ, 0 ≤ t → absoluteError t ≤ K) :
    ‖(L : ℂ)*coprimeInner ⌊Real.exp (L*u)⌋₊ g L u θ P A‖ ≤
      coprimeCap P θ C U K *
        SupportProductTail.supportedSum g (Finset.Icc 1 ⌊Real.exp (L*u)⌋₊) (fun r => 1/(r : ℝ)) := by
  rw [scaled_coprime_expansion L u θ g P A hL.ne']
  unfold SupportProductTail.supportedSum
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro r hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
  have hr0 : 0 < (r : ℝ) := lt_of_lt_of_le zero_lt_one hr1
  have hrx : (r : ℝ) ≤ Real.exp (L*u) :=
    (Nat.le_floor_iff (Real.exp_pos _).le).mp (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).2
  have ht : Real.log r/L ∈ Set.Icc 0 u :=
    ShiftWeights.normalized_log_mem r L u hr1 hL ((Real.log_le_iff_le_exp hr0).mpr hrx)
  have huv : u-Real.log r/L ∈ Set.Icc 0 U := ⟨by linarith [ht.2],by linarith [ht.1,hu.2]⟩
  have he := ShiftWeights.exp_weight_bound A (Real.log r/L) C U hA
    (by rw [abs_of_nonneg ht.1]; exact ht.2.trans hu.2)
  have hb := scaledSum_bound P hP A L (u-Real.log r/L) θ C U K hL hθ hA huv hK hbound
  rw [norm_mul, supportFactor, norm_div, Complex.norm_natCast]
  have hcap := scaledCap_nonneg P θ C U K hθ ((norm_nonneg _).trans hA) (hu.1.trans hu.2) hK
  have h := mul_le_mul (div_le_div_of_nonneg_right he hr0.le) hb (norm_nonneg _)
    (div_nonneg (Real.exp_pos _).le hr0.le)
  convert h using 1 <;> unfold coprimeCap <;> ring

/-- The bounding constant is supplied by the proved PNT bridge, not a premise. -/
theorem scaledSum_uniform_bounded (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 ≤ U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ L : ℝ, 0 < L → ∀ u ∈ Set.Icc 0 U,
      ∀ A : ℂ, ‖A‖ ≤ C → ‖scaledSum L u θ P A‖ ≤ B := by
  obtain ⟨K,hK,hbound⟩ := absoluteError_bounded
  exact ⟨scaledCap P θ C U K, scaledCap_nonneg P θ C U K hθ hC hU hK,
    fun L hL u hu A hA => scaledSum_bound P hP A L u θ C U K hL hθ hA hu hK hbound⟩

/-- Enlarge all actual cutoffs to a common one before harmonic averaging. -/
theorem scaled_coprime_common_bound (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (A : ℂ) (g : ℕ) (L u θ C U K : ℝ) (hL : 0 < L) (hθ : 0 < θ)
    (hA : ‖A‖ ≤ C) (hu : u ∈ Set.Icc 0 U) (hK : 0 ≤ K)
    (hbound : ∀ t : ℝ, 0 ≤ t → absoluteError t ≤ K) :
    ‖(L : ℂ)*coprimeInner ⌊Real.exp (L*u)⌋₊ g L u θ P A‖ ≤
      coprimeCap P θ C U K *
        SupportProductTail.supportedSum g (Finset.Icc 1 ⌊Real.exp (L*U)⌋₊) (fun r => 1/(r : ℝ)) := by
  apply (scaled_coprime_bound P hP A g L u θ C U K hL hθ hA hu hK hbound).trans
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (Real.exp_pos _).le (scaledCap_nonneg P θ C U K hθ
      ((norm_nonneg _).trans hA) (hu.1.trans hu.2) hK))
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset_filter _ (Finset.Icc_subset_Icc le_rfl
      (Nat.floor_mono (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 hL.le))))
  · intros; positivity

/-- An unconditional second-moment bound for the actual coprime sums.
Cutoffs may depend arbitrarily on g, including u_g=0. This does not yet
assert that a thin endpoint region has vanishing harmonic mass. -/
theorem coprime_second_moment (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 ≤ U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (L : ℝ), 0 < L → ∀ (N : ℕ) (u : ℕ → ℝ) (A : ℂ),
      ‖A‖ ≤ C → (∀ g ∈ Finset.Icc 1 N, u g ∈ Set.Icc 0 U) →
      (∑ g ∈ Finset.Icc 1 N, (1/(g : ℝ))*
        ‖(L : ℂ)*coprimeInner ⌊Real.exp (L*u g)⌋₊ g L (u g) θ P A‖^2) ≤
          SupportTail.harmonic N * B := by
  obtain ⟨K,hK,hbound⟩ := absoluteError_bounded
  let B := coprimeCap P θ C U K
  have hB : 0 ≤ B := mul_nonneg (Real.exp_pos _).le (scaledCap_nonneg P θ C U K hθ hC hU hK)
  refine ⟨B^2*SupportProductTail.productConstant, by unfold SupportProductTail.productConstant; positivity, ?_⟩
  intro L hL N u A hA hu
  let s := Finset.Icc 1 ⌊Real.exp (L*U)⌋₊
  have hs : ∀ r ∈ s, r ≠ 0 := fun r hr => Nat.ne_of_gt
    (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hr).1)
  have hb : ∀ r ∈ s, B/(r : ℝ) ≤ B*(r : ℝ)^(-3/4 : ℝ) := by
    intro r hr
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (Finset.mem_Icc.mp hr).1
    have hh := SupportTail.rankin_point r 1 (1/4) (by norm_num) hr1 (by norm_num)
    have hh' : 1/(r : ℝ) ≤ (r : ℝ)^(-3/4 : ℝ) := by norm_num at hh ⊢; exact hh
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hh' hB
  have hprod := SupportProductTail.supported_product_bound N s s (fun r => B/r) (fun r => B/r)
    B B hB hB hs hs (by intros; positivity) (by intros; positivity) hb hb
  calc
    _ ≤ ∑ g ∈ Finset.Icc 1 N, (1/(g : ℝ))*
        SupportProductTail.supportedSum g s (fun r => B/r)*
        SupportProductTail.supportedSum g s (fun r => B/r) := by
      apply Finset.sum_le_sum
      intro g hg
      have hh := scaled_coprime_common_bound P hP A g L (u g) θ C U K hL hθ hA (hu g hg) hK hbound
      have he : SupportProductTail.supportedSum g s (fun r => B/r) =
          B*SupportProductTail.supportedSum g s (fun r => 1/r) := by
        simp only [SupportProductTail.supportedSum, Finset.mul_sum, mul_one_div]
      rw [← he] at hh
      have hnon := (norm_nonneg _).trans hh
      have hsq := mul_self_le_mul_self (norm_nonneg _) hh
      simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 1/(g : ℝ))
    _ ≤ _ := by simpa only [pow_two] using hprod

#print axioms scaledSum_uniform_bounded
#print axioms scaled_coprime_common_bound
#print axioms coprime_second_moment
#print axioms absoluteError_bounded
#print axioms mainTerm_bound
#print axioms scaledSum_bound
#print axioms scaled_coprime_bound
end XiPrime8845.ShiftedEndpoint

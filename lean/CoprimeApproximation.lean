import CoprimeHead

/-! Actual coprime sums: finite-head main term and product-safe error envelopes.
All conclusions here stay away from u=0; endpoint boundedness is separate. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace XiPrime8845.CoprimeApproximation
open ShiftWeights WeightDerivatives WeightedMobius ShiftedMobius CoprimeShift
open ShiftedEndpoint CoprimeHead SupportProductTail
attribute [local instance] Classical.propDecidable

def actual (L : ℝ) (g : ℕ) (u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℂ :=
  (L : ℂ)*coprimeInner ⌊Real.exp (L*u)⌋₊ g L u θ P A

theorem term_bound (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (A : ℂ) (r : ℕ) (L u θ C U K : ℝ) (hL : 0 < L) (hθ : 0 < θ)
    (hA : ‖A‖ ≤ C) (hu : u ∈ Set.Icc 0 U) (hK : 0 ≤ K)
    (hbound : ∀ t : ℝ, 0 ≤ t → absoluteError t ≤ K)
    (hr : r ∈ Finset.Icc 1 ⌊Real.exp (L*u)⌋₊) :
    ‖supportFactor r L A * scaledSum L (u-Real.log r/L) θ P A‖ ≤
      coprimeCap P θ C U K/(r : ℝ) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (Finset.mem_Icc.mp hr).1
  have hr0 := lt_of_lt_of_le zero_lt_one hr1
  have hrx := (Nat.le_floor_iff (Real.exp_pos (L*u)).le).mp (Finset.mem_Icc.mp hr).2
  have ht := normalized_log_mem r L u hr1 hL ((Real.log_le_iff_le_exp hr0).mpr hrx)
  have he := exp_weight_bound A (Real.log r/L) C U hA
    (by rw [abs_of_nonneg ht.1]; exact ht.2.trans hu.2)
  have hb := scaledSum_bound P hP A L (u-Real.log r/L) θ C U K hL hθ hA
    ⟨by linarith [ht.2],by linarith [ht.1,hu.2]⟩ hK hbound
  rw [norm_mul, supportFactor, norm_div, Complex.norm_natCast]
  have hh := mul_le_mul (div_le_div_of_nonneg_right he hr0.le) hb (norm_nonneg _)
    (div_nonneg (Real.exp_pos _).le hr0.le)
  simpa only [coprimeCap, div_mul_eq_mul_div] using hh

theorem headMain_extend (Q N g : ℕ) (hQN : Q ≤ N) (u θ : ℝ)
    (P : Polynomial ℂ) (A : ℂ) :
    headMain Q g u θ P A =
      ∑ r ∈ (Finset.Icc 1 N).filter (SmoothMobius.supported g),
        if r ≤ Q then mainTerm u θ P A/r else 0 := by
  unfold headMain
  symm
  rw [← Finset.sum_filter]
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1,hN⟩,hs⟩,hQ⟩
    exact ⟨⟨h1,hQ⟩,hs⟩
  · rintro ⟨⟨h1,hQ⟩,hs⟩
    exact ⟨⟨⟨h1,hQ.trans hQN⟩,hs⟩,hQ⟩

def errorCoeff (eps B : ℝ) (Q : ℕ) (r : ℕ) : ℝ :=
  eps/(r : ℝ) + if Q ≤ r then B/(r : ℝ) else 0

/-- The eps/head plus Rankin/tail coefficient bound is now supplied for the
actual arithmetic sum, uniformly in g and in the interior cutoff. -/
theorem head_approximation_envelope (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C u₀ U K : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hu₀ : 0 < u₀) (hU : 0 < U)
    (hK : 0 ≤ K) (hbound : ∀ t : ℝ, 0 ≤ t → absoluteError t ≤ K)
    (Q : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ L : ℝ in atTop, ∀ g : ℕ, ∀ A : ℂ, ‖A‖ ≤ C → ∀ u ∈ Set.Icc u₀ U,
      ‖actual L g u θ P A-headMain Q g u θ P A‖ ≤
        supportedSum g (Finset.Icc 1 ⌊Real.exp (L*U)⌋₊)
          (errorCoeff eps (coprimeCap P θ C U K) Q) := by
  have hB : 0 ≤ coprimeCap P θ C U K := mul_nonneg (Real.exp_pos _).le
    (scaledCap_nonneg P θ C U K hθ hC hU.le hK)
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    finite_head_eventually P hP θ C u₀ U hθ hC hu₀ hU Q eps heps,
    finite_head_in_cutoff Q u₀ hu₀] with L hL hhead hcut
  intro g A hA u hu
  have hu0 : u ∈ Set.Icc 0 U := ⟨hu₀.le.trans hu.1,hu.2⟩
  rw [actual, scaled_coprime_expansion L u θ g P A hL.ne',
    headMain_extend Q _ g (hcut u hu.1), ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ supportedSum g (Finset.Icc 1 ⌊Real.exp (L*u)⌋₊)
        (errorCoeff eps (coprimeCap P θ C U K) Q) := by
      apply Finset.sum_le_sum
      intro r hr
      have hr' := (Finset.mem_filter.mp hr).1
      by_cases hrQ : r ≤ Q
      · rw [if_pos hrQ]
        apply (hhead r (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr').1,hrQ⟩) A hA u hu).trans
        unfold errorCoeff
        apply le_add_of_nonneg_right
        split_ifs <;> positivity
      · rw [if_neg hrQ, sub_zero]
        apply (term_bound P hP A r L u θ C U K hL hθ hA hu0 hK hbound hr').trans
        unfold errorCoeff
        rw [if_pos (by omega)]
        have : 0 ≤ eps/(r : ℝ) := by positivity
        linarith
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset_filter _ (Finset.Icc_subset_Icc le_rfl
          (Nat.floor_mono (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 hL.le))))
      · intro r _ _
        unfold errorCoeff
        split_ifs <;> positivity

theorem errorCoeff_rootBound (s : Finset ℕ) (eps B : ℝ) (Q : ℕ)
    (heps : 0 ≤ eps) (hB : 0 ≤ B) (hQ : 0 < Q) (hs : ∀ r ∈ s, r ≠ 0) :
    RootBound s (errorCoeff eps B Q) (eps+B*(Q : ℝ)^(-1/4 : ℝ)) := by
  change RootBound s (fun r => eps/(r : ℝ) + if Q ≤ r then B/(r : ℝ) else 0) _
  simpa only [Nat.cast_le] using
    head_tail_rootBound s eps B Q heps hB (by exact_mod_cast hQ) hs

theorem reciprocal_rootBound (s : Finset ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hs : ∀ r ∈ s, r ≠ 0) : RootBound s (fun r => B/(r : ℝ)) B := by
  simpa only [zero_div, ite_self, add_zero, zero_mul] using
    head_tail_rootBound s B 0 1 hB (by norm_num) (by norm_num) hs

theorem headMain_bound (Q N g : ℕ) (hQN : Q ≤ N) (P : Polynomial ℂ) (A : ℂ)
    (u θ C U : ℝ) (hθ : 0 < θ) (hA : ‖A‖ ≤ C) (hu : u ∈ Set.Icc 0 U) :
    ‖headMain Q g u θ P A‖ ≤
      supportedSum g (Finset.Icc 1 N) (fun r => firstCap P θ C U/(r : ℝ)) := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ supportedSum g (Finset.Icc 1 Q) (fun r => firstCap P θ C U/(r : ℝ)) := by
      apply Finset.sum_le_sum
      intro r hr
      rw [norm_div, Complex.norm_natCast]
      exact div_le_div_of_nonneg_right (mainTerm_bound P A u θ C U hθ hA hu) (by positivity)
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset_filter _ (Finset.Icc_subset_Icc le_rfl hQN)
      · intro r _ _
        exact div_nonneg (firstCap_nonneg P θ C U hθ ((norm_nonneg A).trans hA)
          (hu.1.trans hu.2)) (by positivity)

/-- Actual two-profile products are returned to the harmonic g-average.
The explicit error can be made small by taking Q large, then eps small, then L
large. This is an interior finite-head theorem, not the outer gcd main term. -/
theorem coprime_product_error_eventually (P G : Polynomial ℂ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (θ C u₀ U K : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hu₀ : 0 < u₀) (hU : 0 < U)
    (hK : 0 ≤ K) (hbound : ∀ t : ℝ, 0 ≤ t → absoluteError t ≤ K)
    (Q : ℕ) (hQ : 0 < Q) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) (u v : ℕ → ℝ) (A B : ℂ),
      ‖A‖ ≤ C → ‖B‖ ≤ C →
      (∀ g ∈ Finset.Icc 1 N, u g ∈ Set.Icc u₀ U) →
      (∀ g ∈ Finset.Icc 1 N, v g ∈ Set.Icc u₀ U) →
      (∑ g ∈ Finset.Icc 1 N, (1/(g : ℝ))*
        ‖actual L g (u g) θ P A * actual L g (v g) θ G B -
          headMain Q g (u g) θ P A * headMain Q g (v g) θ G B‖) ≤
      SupportTail.harmonic N *
        (((eps+coprimeCap P θ C U K*(Q : ℝ)^(-1/4 : ℝ))*coprimeCap G θ C U K +
          firstCap P θ C U*(eps+coprimeCap G θ C U K*(Q : ℝ)^(-1/4 : ℝ)))*productConstant) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    head_approximation_envelope P hP θ C u₀ U K hθ hC hu₀ hU hK hbound Q eps heps,
    head_approximation_envelope G hG θ C u₀ U K hθ hC hu₀ hU hK hbound Q eps heps,
    finite_head_in_cutoff Q U hU] with L hL hleft hright hcut
  intro N u v A B hA hB hu hv
  let s := Finset.Icc 1 ⌊Real.exp (L*U)⌋₊
  have hs : ∀ r ∈ s, r ≠ 0 := fun r hr => Nat.ne_of_gt
    (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hr).1)
  have hcap (F : Polynomial ℂ) : 0 ≤ coprimeCap F θ C U K :=
    mul_nonneg (Real.exp_pos _).le (scaledCap_nonneg F θ C U K hθ hC hU.le hK)
  apply product_error_average N s s
    (fun g => actual L g (u g) θ P A) (fun g => actual L g (v g) θ G B)
    (fun g => headMain Q g (u g) θ P A) (fun g => headMain Q g (v g) θ G B)
    (fun r => firstCap P θ C U/r) (fun r => coprimeCap G θ C U K/r)
    (errorCoeff eps (coprimeCap P θ C U K) Q) (errorCoeff eps (coprimeCap G θ C U K) Q)
    (firstCap P θ C U) (coprimeCap G θ C U K)
    (eps+coprimeCap P θ C U K*(Q : ℝ)^(-1/4 : ℝ))
    (eps+coprimeCap G θ C U K*(Q : ℝ)^(-1/4 : ℝ)) hs hs
    (reciprocal_rootBound s _ (firstCap_nonneg P θ C U hθ hC hU.le) hs)
    (reciprocal_rootBound s _ (hcap G) hs)
    (errorCoeff_rootBound s _ _ Q heps.le (hcap P) hQ hs)
    (errorCoeff_rootBound s _ _ Q heps.le (hcap G) hQ hs)
  · intro g hg
    exact headMain_bound Q _ g (hcut U le_rfl) P A (u g) θ C U hθ hA
      ⟨hu₀.le.trans (hu g hg).1,(hu g hg).2⟩
  · intro g hg
    have hh := scaled_coprime_common_bound G hG B g L (v g) θ C U K hL hθ hB
      ⟨hu₀.le.trans (hv g hg).1,(hv g hg).2⟩ hK hbound
    simpa only [actual, supportedSum, Finset.mul_sum, mul_one_div] using hh
  · exact fun g hg => hleft g A hA (u g) (hu g hg)
  · exact fun g hg => hright g B hB (v g) (hv g hg)

#print axioms coprime_product_error_eventually
#print axioms headMain_bound
#print axioms reciprocal_rootBound
#print axioms term_bound
#print axioms headMain_extend
#print axioms head_approximation_envelope
#print axioms errorCoeff_rootBound
end XiPrime8845.CoprimeApproximation

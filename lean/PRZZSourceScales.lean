import PRZZActualBranchCells

/-! Numerical orientation and upper-box inflation for PRZZ section 4.
Type II uses the smaller of the two lower product scales. The short
Mobius cutoff condition is still explicit, not inferred from N alone. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZSourceScales
open PRZZActualBranchCells PRZZHBBranches PRZZBranchGrouping
set_option maxHeartbeats 2000000

theorem smaller_balanced (e f U W : ℝ) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hp : e*f = U) (hWe : W ≤ e) (hWf : W ≤ f) :
    W ≤ min e f ∧ min e f ≤ U^(1/2:ℝ) := by
  have hU : 0 ≤ U := hp ▸ mul_nonneg he hf
  have hm : 0 ≤ min e f := le_min he hf
  have hs : (min e f)^2 ≤ U := by
    have hh := mul_le_mul (min_le_left e f) (min_le_right e f) hm he
    nlinarith
  have hsq := Real.sq_sqrt hU
  have hn := Real.sqrt_nonneg U
  rw [Real.sqrt_eq_rpow] at hsq hn
  exact ⟨le_min hWe hWf,by nlinarith⟩

theorem upper_product (b : Branch) (k : Fin b.2.length → ℕ)
    (s : Finset (Fin b.2.length)) :
    (∏ i ∈ s, (2:ℝ)^(k i+1)) = 2^s.card*(∏ i ∈ s, (2:ℝ)^(k i)) := by
  simp_rw [pow_succ]
  rw [prod_mul_distrib,prod_const,mul_comm]

/-- A common branch-length constant controls both DI upper boxes and
their product. All factors, including duplicate occurrences, are counted. -/
theorem oriented_boxes (y K : ℕ) (js : List ℕ) (b : Branch) (hb : b ∈ branches y K js)
    (k : Fin b.2.length → ℕ) (s : Finset (Fin b.2.length)) (U W : ℝ)
    (hp : ∏ i, (2:ℝ)^(k i) = U)
    (h1 : W ≤ ∏ i ∈ s, (2:ℝ)^(k i))
    (h2 : W ≤ ∏ i ∈ univ \ s, (2:ℝ)^(k i)) :
    ∃ t : Finset (Fin b.2.length),
      W ≤ ∏ i ∈ t, (2:ℝ)^(k i) ∧
      (∏ i ∈ t, (2:ℝ)^(k i)) ≤ U^(1/2:ℝ) ∧
      (∏ i ∈ t, (2:ℝ)^(k i+1)) ≤ (2:ℝ)^((js.length+1)*(2*K))*U^(1/2:ℝ) ∧
      (∏ i ∈ t, (2:ℝ)^(k i+1))*(∏ i ∈ univ \ t, (2:ℝ)^(k i+1)) ≤
        (2:ℝ)^((js.length+1)*(2*K))*U := by
  classical
  have he : (∏ i ∈ s, (2:ℝ)^(k i))*(∏ i ∈ univ \ s, (2:ℝ)^(k i)) = U :=
    (subset_product univ s (subset_univ s) _).symm.trans hp
  have hm := smaller_balanced _ _ U W (by positivity) (by positivity) he h1 h2
  have hex : ∃ t : Finset (Fin b.2.length), W ≤ ∏ i ∈ t, (2:ℝ)^(k i) ∧
      (∏ i ∈ t, (2:ℝ)^(k i)) ≤ U^(1/2:ℝ) := by
    by_cases hh : (∏ i ∈ s, (2:ℝ)^(k i)) ≤ ∏ i ∈ univ \ s, (2:ℝ)^(k i)
    · exact ⟨s,h1,by simpa only [min_eq_left hh] using hm.2⟩
    · exact ⟨univ \ s,h2,by simpa only [min_eq_right (le_of_not_ge hh)] using hm.2⟩
  obtain ⟨t,ht,htu⟩ := hex
  have hlen := PRZZBranchDegrees.branches_length y K js b hb
  have hcard : t.card ≤ (js.length+1)*(2*K) :=
    (card_le_card (subset_univ t)).trans (by simpa using hlen)
  have hc : (2:ℝ)^t.card ≤ 2^((js.length+1)*(2*K)) :=
    pow_le_pow_right₀ (by norm_num) hcard
  refine ⟨t,ht,htu,?_,?_⟩
  · rw [upper_product]
    exact mul_le_mul hc htu (by positivity) (by positivity)
  · rw [← subset_product univ t (subset_univ t),upper_product]
    simp only [card_univ,Fintype.card_fin]
    rw [hp]
    have hU : 0 ≤ U := hp ▸ (show 0 ≤ ∏ i, (2:ℝ)^(k i) by positivity)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hlen) hU

#print axioms smaller_balanced
#print axioms upper_product
#print axioms oriented_boxes

/-- Supplies the source's W=U^(1/4) scale hypotheses. The root-cutoff
comparison is stated explicitly because it is not true for every small U. -/
theorem quarter_conditions (U y : ℝ) (hU : 1 < U) (hy : y ≤ U^(3/4:ℝ)) :
    1 < U^(1/4:ℝ) ∧ (U^(1/4:ℝ))^3 ≤ U ∧ y ≤ U/U^(1/4:ℝ) := by
  have hU0 : 0 < U := zero_lt_one.trans hU
  have he : U/U^(1/4:ℝ) = U^(3/4:ℝ) := by
    rw [show (3/4:ℝ)=1-1/4 by norm_num,Real.rpow_sub hU0,Real.rpow_one]
  refine ⟨Real.one_lt_rpow hU (by norm_num),?_,by rwa [he]⟩
  rw [← Real.rpow_mul_natCast hU0.le]
  norm_num
  simpa using Real.rpow_le_rpow_of_exponent_le hU.le (show (3/4:ℝ) ≤ 1 by norm_num)

#print axioms quarter_conditions

/-- A local HB root cutoff supplies the short-factor comparison on the
large-scale range. The local expansion length x is not replaced by N. -/
theorem local_root_short (K : ℕ) (x U : ℝ) (hK : 4 ≤ K)
    (hx : 1 ≤ x) (hU : 1 ≤ U) (hxU : x ≤ U^2) :
    (⌊x^((K:ℝ)⁻¹)⌋₊:ℝ) ≤ U^(3/4:ℝ) := by
  have hk : (4:ℝ) ≤ K := by exact_mod_cast hK
  have hk0 : 0 < (K:ℝ) := by linarith
  have hki : (K:ℝ)⁻¹ ≤ (1/4:ℝ) := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hk0).mpr (by linarith)
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  calc
    _ ≤ x^((K:ℝ)⁻¹) := Nat.floor_le (Real.rpow_nonneg (by linarith) _)
    _ ≤ x^(1/4:ℝ) := Real.rpow_le_rpow_of_exponent_le hx hki
    _ ≤ (U^2)^(1/4:ℝ) := Real.rpow_le_rpow (by linarith) hxU (by norm_num)
    _ = U^(1/2:ℝ) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hU0.le]
      norm_num
    _ ≤ U^(3/4:ℝ) := Real.rpow_le_rpow_of_exponent_le hU (by norm_num)

/-- For x=c*U, the sole extra size threshold is U>=c. Since c is a
branch-length constant, this does not impose a height-growing threshold. -/
theorem local_root_quarter (K : ℕ) (c U : ℝ) (hK : 4 ≤ K)
    (hc : 1 ≤ c) (hU : 1 < U) (hlarge : c ≤ U) :
    1 < U^(1/4:ℝ) ∧ (U^(1/4:ℝ))^3 ≤ U ∧
      (⌊(c*U)^((K:ℝ)⁻¹)⌋₊:ℝ) ≤ U/U^(1/4:ℝ) := by
  apply quarter_conditions U _ hU
  apply local_root_short K (c*U) U hK (one_le_mul_of_one_le_of_one_le hc hU.le) hU.le
  nlinarith

#print axioms local_root_short
#print axioms local_root_quarter

/-- The large-scale local HB configuration supplies the classifier's
numeric premises and orients its actual Type II groups. Type I and zero
cells are retained. Small U is deliberately not included in this theorem. -/
theorem local_layout (N K : ℕ) (js : List ℕ) (U : ℝ) (hK : 4 ≤ K)
    (hU : 1 < U) (hlarge : (2:ℝ)^((js.length+1)*(2*K)) ≤ U)
    (b : Branch)
    (hb : b ∈ branches ⌊((2:ℝ)^((js.length+1)*(2*K))*U)^((K:ℝ)⁻¹)⌋₊ K js)
    (k : Fin b.2.length → ℕ) (hp : ∏ i, (2:ℝ)^(k i) = U) :
    group N b k univ = 0 ∨
    (∃ i, (∃ J a, PRZZTypedClassification.Free a ∧
      factor b i = PRZZWeightedHeathBrown.weight J (PRZZGroupBounds.atom a)) ∧
      U/U^(1/4:ℝ) < (2:ℝ)^(k i) ∧
      (∏ j ∈ univ.erase i, (2:ℝ)^(k j)) < U^(1/4:ℝ)) ∨
    (∃ t : Finset (Fin b.2.length),
      U^(1/4:ℝ) ≤ ∏ i ∈ t, (2:ℝ)^(k i) ∧
      (∏ i ∈ t, (2:ℝ)^(k i)) ≤ U^(1/2:ℝ) ∧
      (∏ i ∈ t, (2:ℝ)^(k i+1)) ≤ (2:ℝ)^((js.length+1)*(2*K))*U^(1/2:ℝ) ∧
      (∏ i ∈ t, (2:ℝ)^(k i+1))*(∏ i ∈ univ \ t, (2:ℝ)^(k i+1)) ≤
        (2:ℝ)^((js.length+1)*(2*K))*U ∧
      group N b k univ = group N b k t * group N b k (univ \ t)) := by
  have hc : (1:ℝ) ≤ 2^((js.length+1)*(2*K)) := one_le_pow₀ (by norm_num)
  obtain ⟨hW,hscale,hshort⟩ := local_root_quarter K _ U hK hc hU hlarge
  rcases PRZZActualBranchCells.classify N _ K js b hb k U (U^(1/4:ℝ)) hW hp hscale hshort with
    hz | hi | ⟨s,h1,_,h2,_,_⟩
  · exact Or.inl hz
  · exact Or.inr (Or.inl hi)
  · obtain ⟨t,ht,htu,hbox,hprod⟩ := oriented_boxes _ K js b hb k s U (U^(1/4:ℝ)) hp h1 h2
    exact Or.inr (Or.inr ⟨t,ht,htu,hbox,hprod,group_split N b k t⟩)

#print axioms local_layout
end XiPrime8845.PRZZSourceScales

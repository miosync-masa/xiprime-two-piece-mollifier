import PRZZEffectiveBalance
import PRZZRowPlacement

/-! Placement for actual row-local HB cells. A nonzero retained sample
supplies the root-cutoff comparison; no equality of branch lists with a
different cutoff is used. Bounded small scales remain a separate case. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZRowCellLayout
open PRZZActualBranchCells PRZZHBBranches PRZZActualSupportBoxes PRZZBranchGrouping
set_option maxHeartbeats 2000000

theorem cutoff_le (N d h j K : ℕ) (js : List ℕ) (hh : 0 < h)
    (b : Branch)
    (hb : b ∈ branches ⌊(PRZZRowWindow.hi N d h j:ℝ)^((K:ℝ)⁻¹)⌋₊ K js)
    (k : Fin b.2.length → ℕ) (U : ℝ) (hp : ∏ i, (2:ℝ)^(k i) = U)
    (n : ℕ) (hl : PRZZRowWindow.lo h j ≤ n) (hz : group N b k univ n ≠ 0) :
    (PRZZRowWindow.hi N d h j:ℝ) ≤ 2*((2:ℝ)^((js.length+1)*(2*K)))*U := by
  have hn := (group_support N b k univ n hz).2
  have hn' : (n:ℝ) ≤ ∏ i, (2:ℝ)^(k i+1) := by exact_mod_cast hn
  have hlen := PRZZBranchDegrees.branches_length _ K js b hb
  have hbox : (n:ℝ) ≤ (2:ℝ)^((js.length+1)*(2*K))*U := by
    apply hn'.trans
    rw [PRZZSourceScales.upper_product, hp]
    simp only [card_univ,Fintype.card_fin]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hlen)
      (hp ▸ (by positivity : (0:ℝ) ≤ ∏ i, (2:ℝ)^(k i)))
  have ht : (PRZZRowWindow.hi N d h j:ℝ) < 2*PRZZRowWindow.lo h j := by
    exact_mod_cast PRZZRowPlacement.narrow N d h j hh
  have hl' : (PRZZRowWindow.lo h j:ℝ) ≤ n := by exact_mod_cast hl
  nlinarith

/-- Every cell that meets the actual retained row is either bounded-small,
has a genuine free Type I factor, or supplies effective balanced DI boxes. -/
theorem actual_layout (N d h j K : ℕ) (js : List ℕ) (hh : 0 < h) (hK : 4 ≤ K)
    (b : Branch)
    (hb : b ∈ branches ⌊(PRZZRowWindow.hi N d h j:ℝ)^((K:ℝ)⁻¹)⌋₊ K js)
    (k : Fin b.2.length → ℕ) (U : ℝ) (hp : ∏ i, (2:ℝ)^(k i) = U)
    (n : ℕ) (hn : n ≤ N) (hl : PRZZRowWindow.lo h j ≤ n)
    (hu : n ≤ PRZZRowWindow.hi N d h j) (hz : group N b k univ n ≠ 0) :
    U ≤ 2*((2:ℝ)^((js.length+1)*(2*K))) ∨
    (∃ i, (∃ J a, PRZZTypedClassification.Free a ∧
      factor b i = PRZZWeightedHeathBrown.weight J (PRZZGroupBounds.atom a)) ∧
      U/U^(1/4:ℝ) < (2:ℝ)^(k i) ∧
      (∏ r ∈ univ.erase i, (2:ℝ)^(k r)) < U^(1/4:ℝ)) ∨
    (∃ s : Finset (Fin b.2.length),
      0 ≤ (upper N b k s:ℝ)*(upper N b k (univ \ s):ℝ) ∧
      U^(1/4:ℝ) ≤ (upper N b k s:ℝ) ∧
      (upper N b k s:ℝ) ≤ (2:ℝ)^((js.length+1)*(2*K))*U^(1/2:ℝ) ∧
      (upper N b k s:ℝ)*(upper N b k (univ \ s):ℝ) ≤ (2:ℝ)^((js.length+1)*(2*K))*U ∧
      group N b k univ = group N b k s*group N b k (univ \ s)) := by
  by_cases hsmall : U ≤ 2*((2:ℝ)^((js.length+1)*(2*K)))
  · exact Or.inl hsmall
  have hc : (1:ℝ) ≤ 2^((js.length+1)*(2*K)) := one_le_pow₀ (by norm_num)
  have hU : 1 < U := by linarith
  have hx : (1:ℝ) ≤ PRZZRowWindow.hi N d h j := by
    exact_mod_cast (show 1 ≤ PRZZRowWindow.hi N d h j from
      (show (1:ℕ) ≤ PRZZRowWindow.lo h j from Nat.succ_le_succ (Nat.zero_le _)).trans (hl.trans hu))
  have hxU : (PRZZRowWindow.hi N d h j:ℝ) ≤ U^2 := by
    have ht := cutoff_le N d h j K js hh b hb k U hp n hl hz
    nlinarith
  have hshort := PRZZSourceScales.local_root_short K _ U hK hx hU.le hxU
  obtain ⟨hW,hscale,hs⟩ := PRZZSourceScales.quarter_conditions U _ hU hshort
  rcases classify N _ K js b hb k U (U^(1/4:ℝ)) hW hp hscale hs with
    hzero | hi | ⟨s,h1,_,h2,_,_⟩
  · exact (hz (by rw [hzero]; rfl)).elim
  · exact Or.inr (Or.inl hi)
  · obtain ⟨s,hs,_,he,hy⟩ := PRZZSourceScales.oriented_boxes _ K js b hb k s U _ hp h1 h2
    obtain ⟨h0,h1,h2,h3⟩ := PRZZEffectiveBalance.clipped N b k s U _ hU.le
      (PRZZEffectiveBalance.scale_le N b k U hp n hn hz) hs he hy
    exact Or.inr (Or.inr ⟨s,h0,h1,h2,h3,group_split N b k s⟩)

/-- The literal row supplies the vanishing hypothesis for ALL branches
and dyadic cells at the same cutoff used by actual_layout. -/
theorem row_expansion (N d h j K : ℕ) (js : List ℕ) (hd : 0 < d) (hh : 0 < h)
    (hK : 0 < K) (F1 : ℝ → ℂ) (alpha : ℂ) (t : ℝ) (F : ℕ → ℂ) :
    (∑ n ∈ Icc 1 N, (if d.Coprime n then
      PRZZResidualRow.weight N d j h F1 alpha t n*F n else 0)*
        (PRZZGCoefficient.coefficient js n:ℂ)) =
    ((branches ⌊(PRZZRowWindow.hi N d h j:ℝ)^((K:ℝ)⁻¹)⌋₊ K js).map
      (fun b => ∑ k : Fin b.2.length → Fin (Nat.log 2 N+1), ∑ n ∈ Icc 1 N,
        (if d.Coprime n then PRZZResidualRow.weight N d j h F1 alpha t n*F n else 0)*
        (b.1:ℂ)*(group N b (fun i => (k i).val) univ n:ℂ))).sum := by
  apply PRZZAllBranchCells.local_all N (PRZZRowWindow.hi N d h j) K js hK
  intro n hn hlarge
  rw [PRZZRowWindow.weight_eq N d h j hd hh]
  simp [PRZZMaskedVariation.mask,not_le.mpr hlarge]

/-- A genuinely nonzero weighted cell supplies a retained sample; no
support witness is assumed by the caller. The remaining factor F may
contain all additional coprimality, phase and right-coefficient weights. -/
theorem retained_sample (N d h j : ℕ) (hd : 0 < d) (hh : 0 < h)
    (b : Branch) (k : Fin b.2.length → ℕ) (F1 : ℝ → ℂ)
    (alpha : ℂ) (t : ℝ) (F : ℕ → ℂ)
    (hz : (∑ n ∈ Icc 1 N, PRZZResidualRow.weight N d j h F1 alpha t n*
      F n*(group N b k univ n:ℂ)) ≠ 0) :
    ∃ n ∈ Icc 1 N, PRZZRowWindow.lo h j ≤ n ∧
      n ≤ PRZZRowWindow.hi N d h j ∧ group N b k univ n ≠ 0 := by
  obtain ⟨n,hn,hnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hw : PRZZResidualRow.weight N d j h F1 alpha t n ≠ 0 := by
    intro he; simp [he] at hnz
  have hg : group N b k univ n ≠ 0 := by intro he; simp [he] at hnz
  have hmem : PRZZRowWindow.lo h j ≤ n ∧ n ≤ PRZZRowWindow.hi N d h j := by
    by_contra he
    apply hw
    rw [PRZZRowWindow.weight_eq N d h j hd hh]
    simp [PRZZMaskedVariation.mask,he]
  exact ⟨n,hn,hmem.1,hmem.2,hg⟩

#print axioms retained_sample
#print axioms cutoff_le
#print axioms actual_layout
#print axioms row_expansion
end XiPrime8845.PRZZRowCellLayout

import PRZZActualBranchCells

/-! Literal HB factors have no hidden arbitrary subset masks. The only
restriction on a free factor is its separately retained dyadic cell.
This strengthens the general typed classification for actual branches. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.zeta
open ArithmeticFunction Finset
namespace XiPrime8845.PRZZBareFactors
open PRZZHBBranches PRZZWeightedHeathBrown PRZZActualBranchCells
set_option maxHeartbeats 2000000

def Bare (y D : ℕ) (f : ArithmeticFunction ℝ) : Prop :=
  ∃ m ≤ D, f = weight m (PRZZHeathBrown.truncatedMu y) ∨
    f = weight m ζ ∨ f = weight m ArithmeticFunction.log

theorem weighted_bare (y : ℕ) (fs : List (ArithmeticFunction ℝ))
    (hf : ∀ f ∈ fs, f = PRZZHeathBrown.truncatedMu y ∨ f = ζ ∨ f = ArithmeticFunction.log)
    (J : ℕ) (b : Branch) (hb : b ∈ weighted J fs) : ∀ f ∈ b.2, Bare y J f := by
  induction fs generalizing J b with
  | nil =>
    simp only [weighted] at hb
    split_ifs at hb
    · simp_all
    · simp at hb
  | cons f fs ih =>
    simp only [weighted,List.mem_flatMap,List.mem_map] at hb
    obtain ⟨k,hk,c,hc,rfl⟩ := hb
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · refine ⟨k,by have := List.mem_range.mp hk; omega,?_⟩
      rcases hf f (by simp) with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · obtain ⟨m,hm,he⟩ := ih (fun g hg => hf g (by simp [hg])) (J-k) c hc g hg
      exact ⟨m,by omega,he⟩

theorem mu_bare (y K : ℕ) (b : Branch) (hb : b ∈ muBranches y K) :
    ∀ f ∈ b.2, Bare y 0 f := by
  simp only [muBranches,List.mem_map] at hb
  obtain ⟨j,hj,rfl⟩ := hb
  intro f hf
  simp only [List.mem_append,List.mem_replicate] at hf
  rcases hf with ⟨_,rfl⟩ | ⟨_,rfl⟩
  · refine ⟨0,le_rfl,Or.inl ?_⟩
    ext n; simp [weight_apply]
  · refine ⟨0,le_rfl,Or.inr (Or.inl ?_)⟩
    ext n; simp [weight_apply]

theorem branches_bare (y K : ℕ) (js : List ℕ) (b : Branch)
    (hb : b ∈ branches y K js) : ∀ f ∈ b.2, Bare y js.sum f := by
  have hl (J : ℕ) (c : Branch) (hc : c ∈ lambdaBranches y K J) :
      ∀ f ∈ c.2, Bare y J f := by
    simp only [lambdaBranches,List.mem_flatMap,List.mem_map] at hc
    obtain ⟨j,hj,c,hc,rfl⟩ := hc
    apply weighted_bare y (factors y j) _ J c hc
    intro f hf
    simp only [factors,List.mem_append,List.mem_replicate,List.mem_singleton] at hf
    rcases hf with (⟨_,rfl⟩ | ⟨_,rfl⟩) | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  induction js generalizing b with
  | nil => exact mu_bare y K b hb
  | cons J js ih =>
    simp only [branches,multiply,List.mem_flatMap,List.mem_map] at hb
    obtain ⟨c,hc,e,he,rfl⟩ := hb
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨m,hm,hf⟩ := ih c hc f hf
      exact ⟨m,by simpa using hm.trans (Nat.le_add_left js.sum J),hf⟩
    · obtain ⟨m,hm,hf⟩ := hl J e he f hf
      exact ⟨m,by simpa using hm.trans (Nat.le_add_right J js.sum),hf⟩

/-- A large nonzero literal factor equals one log power at EVERY positive
integer, not merely at its nonzero witness. -/
theorem large_log_power (y K : ℕ) (js : List ℕ) (b : Branch)
    (hb : b ∈ branches y K js) (f : ArithmeticFunction ℝ) (hf : f ∈ b.2)
    (n : ℕ) (hn : y < n) (hne : f n ≠ 0) :
    ∃ m ≤ js.sum+1, ∀ a : ℕ, 0 < a → f a = (Real.log a)^m := by
  obtain ⟨m,hm,hf⟩ := branches_bare y K js b hb f hf
  rcases hf with rfl | rfl | rfl
  · exfalso
    apply hne
    change Real.log n^m*(if n ≤ y then PRZZ.muReal n else 0) = 0
    rw [if_neg (not_le.mpr hn),mul_zero]
  · refine ⟨m,by omega,?_⟩
    intro a ha
    simp [weight_apply,ArithmeticFunction.zeta_apply,ha.ne']
  · refine ⟨m+1,by omega,?_⟩
    intro a ha
    simp [weight_apply,ArithmeticFunction.log_apply,pow_succ]

/-- Supply the precise dyadic log-power factor consumed by FreeDyadic.
Repeated factors keep their indices. -/
theorem large_piece (N y K : ℕ) (js : List ℕ) (b : Branch)
    (hb : b ∈ branches y K js) (k : Fin b.2.length → ℕ) (i : Fin b.2.length)
    (hn : group N b k univ ≠ 0) (hi : (y:ℝ) < (2:ℝ)^(k i)) :
    ∃ m ≤ js.sum+1, ∀ a : ℕ,
      (piece N b k i a:ℂ) =
        if a ∈ PRZZDyadic.cell N (k i) then (Real.log a:ℂ)^m else 0 := by
  obtain ⟨n,hw⟩ := witnesses N b k hn
  obtain ⟨m,hm,hf⟩ := large_log_power y K js b hb (PRZZBranchGrouping.factor b i)
    (List.getElem_mem i.isLt) (n i) (by exact_mod_cast hi.trans_le (hw i).1) (hw i).2
  refine ⟨m,hm,?_⟩
  intro a
  by_cases ha : a ∈ PRZZDyadic.cell N (k i)
  · have ha0 : 0 < a := (mem_Icc.mp (mem_filter.mp ha).1).1
    have he : piece N b k i a = PRZZBranchGrouping.factor b i a := by
      simp [piece,PRZZBranchEnvelope.mask,ha]
    rw [he,if_pos ha,hf a ha0,Complex.ofReal_pow]
  · simp [piece,PRZZBranchEnvelope.mask,ha]

/-- Every actual cell is zero, has the precise free log-power factor, or
has two complementary balanced groups. No smoothness premise on a
general restricted atom is used. Scale hypotheses remain explicit. -/
theorem classify (N y K : ℕ) (js : List ℕ) (b : Branch)
    (hb : b ∈ branches y K js) (k : Fin b.2.length → ℕ)
    (U W : ℝ) (hW : 1 < W) (hp : ∏ i, (2:ℝ)^(k i) = U)
    (hs : W^3 ≤ U) (hy : (y:ℝ) ≤ U/W) :
    group N b k univ = 0 ∨
    (∃ i, (∃ m ≤ js.sum+1, ∀ a : ℕ, (piece N b k i a:ℂ) =
      if a ∈ PRZZDyadic.cell N (k i) then (Real.log a:ℂ)^m else 0) ∧
      U/W < (2:ℝ)^(k i) ∧ (∏ j ∈ univ.erase i, (2:ℝ)^(k j)) < W) ∨
    (∃ s : Finset (Fin b.2.length),
      W ≤ ∏ i ∈ s, (2:ℝ)^(k i) ∧ (∏ i ∈ s, (2:ℝ)^(k i)) ≤ U/W ∧
      W ≤ ∏ i ∈ univ \ s, (2:ℝ)^(k i) ∧
        (∏ i ∈ univ \ s, (2:ℝ)^(k i)) ≤ U/W ∧
      group N b k univ = group N b k s * group N b k (univ \ s)) := by
  classical
  by_cases hn : group N b k univ = 0
  · exact Or.inl hn
  rcases PRZZDyadic.classify univ (fun i => (2:ℝ)^(k i)) U W hW
    (fun i _ => one_le_pow₀ (by norm_num)) hp hs with h | h
  · obtain ⟨i,hi,hbig,hrest⟩ := h
    exact Or.inr (Or.inl ⟨i,large_piece N y K js b hb k i hn (hy.trans_lt hbig),hbig,hrest⟩)
  · obtain ⟨s,hsub,h1,h2,h3,h4⟩ := h
    exact Or.inr (Or.inr ⟨s,h1,h2,h3,h4,group_split N b k s⟩)

#print axioms classify
#print axioms branches_bare
#print axioms large_log_power
#print axioms large_piece
end XiPrime8845.PRZZBareFactors

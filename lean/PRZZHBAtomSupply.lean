import PRZZHBBranches
import PRZZTypedClassification

/-! Every factor in every actual HB branch has a typed log-weighted atom.
This supplies short-Mobius exclusion, not dyadic support or Type I variation. -/
noncomputable section
open ArithmeticFunction
open scoped ArithmeticFunction.zeta
namespace XiPrime8845.PRZZHBAtomSupply
open PRZZHBBranches PRZZGroupBounds PRZZTypedClassification PRZZWeightedHeathBrown
set_option maxHeartbeats 2000000

def Typed (Y : ℝ) (f : ArithmeticFunction ℝ) : Prop :=
  ∃ J a, Short Y a ∧ f = weight J (atom a)

theorem weighted_supply (Y : ℝ) (fs : List (ArithmeticFunction ℝ))
    (hf : ∀ f ∈ fs, ∃ a, Short Y a ∧ f = atom a) (J : ℕ)
    (b : Branch) (hb : b ∈ weighted J fs) : ∀ f ∈ b.2, Typed Y f := by
  induction fs generalizing J b with
  | nil =>
    simp only [weighted] at hb
    split_ifs at hb with hJ
    · simp only [List.mem_singleton] at hb
      subst b
      simp
    · simp at hb
  | cons f fs ih =>
    simp only [weighted,List.mem_flatMap,List.mem_map] at hb
    obtain ⟨k,hk,c,hc,rfl⟩ := hb
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · obtain ⟨a,ha,rfl⟩ := hf f (by simp)
      exact ⟨k,a,ha,rfl⟩
    · exact ih (fun g hg => hf g (by simp [hg])) (J-k) c hc g hg

theorem mu_supply (y K : ℕ) (b : Branch) (hb : b ∈ muBranches y K) :
    ∀ f ∈ b.2, Typed y f := by
  simp only [muBranches,List.mem_map] at hb
  obtain ⟨j,hj,rfl⟩ := hb
  intro f hf
  simp only [List.mem_append,List.mem_replicate] at hf
  rcases hf with ⟨_,rfl⟩ | ⟨_,rfl⟩
  · refine ⟨0,Atom.mu y,le_rfl,?_⟩
    ext n
    simp [atom,weight_apply]
  · refine ⟨0,Atom.zeta,True.intro,?_⟩
    ext n
    simp [atom,weight_apply]

theorem lambda_supply (y K J : ℕ) (b : Branch) (hb : b ∈ lambdaBranches y K J) :
    ∀ f ∈ b.2, Typed y f := by
  simp only [lambdaBranches,List.mem_flatMap,List.mem_map] at hb
  obtain ⟨j,hj,c,hc,rfl⟩ := hb
  apply weighted_supply y (factors y j) _ J c hc
  intro f hf
  simp only [factors,List.mem_append,List.mem_replicate,List.mem_singleton] at hf
  rcases hf with (⟨_,rfl⟩ | ⟨_,rfl⟩) | rfl
  · exact ⟨Atom.mu y,le_rfl,rfl⟩
  · exact ⟨Atom.zeta,True.intro,rfl⟩
  · exact ⟨Atom.log,True.intro,rfl⟩

theorem branches_supply (y K : ℕ) (js : List ℕ) (b : Branch)
    (hb : b ∈ branches y K js) : ∀ f ∈ b.2, Typed y f := by
  induction js generalizing b with
  | nil => exact mu_supply y K b hb
  | cons J js ih =>
    simp only [branches,multiply,List.mem_flatMap,List.mem_map] at hb
    obtain ⟨c,hc,e,he,rfl⟩ := hb
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact ih c hc f hf
    · exact lambda_supply y K J e he f hf

/-- The large-factor exclusion now applies to literal factors of every
branch. The remaining numeric condition is the short cutoff y <= U/W. -/
theorem branch_large_free (y K : ℕ) (js : List ℕ) (b : Branch)
    (hb : b ∈ branches y K js) (f : ArithmeticFunction ℝ) (hf : f ∈ b.2)
    (n : ℕ) (hn : (y:ℝ) < n) (hne : f n ≠ 0) :
    ∃ J a, Free a ∧ f = weight J (atom a) := by
  obtain ⟨J,a,ha,rfl⟩ := branches_supply y K js b hb f hf
  exact ⟨J,a,large_free a J n y ha hn hne,rfl⟩

/-- Classify any nonzero dyadic tuple of an actual HB branch. The short
cutoff and scale hypotheses remain explicit; no dyadic decomposition or
Type I analytic estimate is smuggled into the classification. -/
theorem branch_classify {ι : Type*} [DecidableEq ι]
    (y K : ℕ) (js : List ℕ) (b : Branch) (hb : b ∈ branches y K js)
    (s : Finset ι) (f : ι → ArithmeticFunction ℝ) (m : ι → ℕ)
    (x : ι → ℝ) (U W : ℝ) (hf : ∀ i ∈ s, f i ∈ b.2)
    (hW : 1 < W) (hx : ∀ i ∈ s, 1 ≤ x i)
    (hprod : ∏ i ∈ s, x i = U) (hscale : W^3 ≤ U)
    (hshort : (y:ℝ) ≤ U/W)
    (hm : ∀ i ∈ s, x i ≤ m i ∧ f i (m i) ≠ 0) :
    (∃ i ∈ s, (∃ J a, Free a ∧ f i = weight J (atom a)) ∧
      U/W < x i ∧ (∏ j ∈ s.erase i, x j) < W) ∨
    (∃ t ⊆ s, W ≤ ∏ i ∈ t, x i ∧ (∏ i ∈ t, x i) ≤ U/W ∧
      W ≤ ∏ i ∈ s \ t, x i ∧ (∏ i ∈ s \ t, x i) ≤ U/W) := by
  rcases PRZZDyadic.classify s x U W hW hx hprod hscale with h | h
  · obtain ⟨i,hi,hbig,hrest⟩ := h
    exact Or.inl ⟨i,hi,branch_large_free y K js b hb (f i) (hf i hi) (m i)
      ((hshort.trans_lt hbig).trans_le (hm i hi).1) (hm i hi).2,hbig,hrest⟩
  · exact Or.inr h

#print axioms branch_classify
#print axioms weighted_supply
#print axioms mu_supply
#print axioms lambda_supply
#print axioms branches_supply
#print axioms branch_large_free
end XiPrime8845.PRZZHBAtomSupply

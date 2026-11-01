import PRZZHBAtomSupply

/-! A common degree ceiling for every literal Heath-Brown branch.
No branch is discarded, and the ceiling is independent of the short cutoff.
This supplies the finite order range needed by source-weight absorption. -/
noncomputable section
open ArithmeticFunction
open scoped ArithmeticFunction.zeta
namespace XiPrime8845.PRZZBranchDegrees
open PRZZHBBranches PRZZGroupBounds PRZZTypedClassification PRZZWeightedHeathBrown
set_option maxHeartbeats 2000000

def Bounded (Y : ℝ) (D : ℕ) (f : ArithmeticFunction ℝ) : Prop :=
  ∃ J a, J ≤ D ∧ Short Y a ∧ f = weight J (atom a)

theorem weighted_degrees (Y : ℝ) (fs : List (ArithmeticFunction ℝ))
    (hf : ∀ f ∈ fs, ∃ a, Short Y a ∧ f = atom a) (J : ℕ)
    (b : Branch) (hb : b ∈ weighted J fs) : ∀ f ∈ b.2, Bounded Y J f := by
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
      exact ⟨k,a,by have := List.mem_range.mp hk; omega,ha,rfl⟩
    · obtain ⟨d,a,hd,ha,he⟩ := ih (fun g hg => hf g (by simp [hg])) (J-k) c hc g hg
      exact ⟨d,a,by omega,ha,he⟩

theorem mu_degrees (y K : ℕ) (b : Branch) (hb : b ∈ muBranches y K) :
    ∀ f ∈ b.2, Bounded y 0 f := by
  simp only [muBranches,List.mem_map] at hb
  obtain ⟨j,hj,rfl⟩ := hb
  intro f hf
  simp only [List.mem_append,List.mem_replicate] at hf
  rcases hf with ⟨_,rfl⟩ | ⟨_,rfl⟩
  · refine ⟨0,Atom.mu y,le_rfl,le_rfl,?_⟩
    ext n
    simp [atom,weight_apply]
  · refine ⟨0,Atom.zeta,le_rfl,True.intro,?_⟩
    ext n
    simp [atom,weight_apply]

theorem lambda_degrees (y K J : ℕ) (b : Branch) (hb : b ∈ lambdaBranches y K J) :
    ∀ f ∈ b.2, Bounded y J f := by
  simp only [lambdaBranches,List.mem_flatMap,List.mem_map] at hb
  obtain ⟨j,hj,c,hc,rfl⟩ := hb
  apply weighted_degrees y (factors y j) _ J c hc
  intro f hf
  simp only [factors,List.mem_append,List.mem_replicate,List.mem_singleton] at hf
  rcases hf with (⟨_,rfl⟩ | ⟨_,rfl⟩) | rfl
  · exact ⟨Atom.mu y,le_rfl,rfl⟩
  · exact ⟨Atom.zeta,True.intro,rfl⟩
  · exact ⟨Atom.log,True.intro,rfl⟩

theorem branches_degrees (y K : ℕ) (js : List ℕ) (b : Branch)
    (hb : b ∈ branches y K js) : ∀ f ∈ b.2, Bounded y js.sum f := by
  induction js generalizing b with
  | nil => exact mu_degrees y K b hb
  | cons J js ih =>
    simp only [branches,multiply,List.mem_flatMap,List.mem_map] at hb
    obtain ⟨c,hc,e,he,rfl⟩ := hb
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨d,a,hd,ha,hf⟩ := ih c hc f hf
      exact ⟨d,a,by simpa using hd.trans (Nat.le_add_left js.sum J),ha,hf⟩
    · obtain ⟨d,a,hd,ha,hf⟩ := lambda_degrees y K J e he f hf
      exact ⟨d,a,by simpa using hd.trans (Nat.le_add_right J js.sum),ha,hf⟩

/-- Large factors in all branches share the same degree ceiling. A free
log atom contributes one additional logarithm in the analytic source. -/
theorem branch_large_free_degrees (y K : ℕ) (js : List ℕ) (b : Branch)
    (hb : b ∈ branches y K js) (f : ArithmeticFunction ℝ) (hf : f ∈ b.2)
    (n : ℕ) (hn : (y:ℝ) < n) (hne : f n ≠ 0) :
    ∃ J a, J ≤ js.sum ∧ Free a ∧ f = weight J (atom a) := by
  obtain ⟨J,a,hJ,ha,rfl⟩ := branches_degrees y K js b hb f hf
  exact ⟨J,a,hJ,large_free a J n y ha hn hne,rfl⟩

theorem weighted_length (fs : List (ArithmeticFunction ℝ)) (J : ℕ)
    (b : Branch) (hb : b ∈ weighted J fs) : b.2.length = fs.length := by
  induction fs generalizing J b with
  | nil =>
    simp only [weighted] at hb
    split_ifs at hb
    · simp_all
    · simp at hb
  | cons f fs ih =>
    simp only [weighted,List.mem_flatMap,List.mem_map] at hb
    obtain ⟨k,hk,c,hc,rfl⟩ := hb
    simpa using congrArg Nat.succ (ih (J-k) c hc)

theorem mu_length (y K : ℕ) (b : Branch) (hb : b ∈ muBranches y K) :
    b.2.length ≤ 2*K := by
  simp only [muBranches,List.mem_map] at hb
  obtain ⟨j,hj,rfl⟩ := hb
  have hj := List.mem_range.mp hj
  simp only [List.length_append,List.length_replicate]
  omega

theorem lambda_length (y K J : ℕ) (b : Branch) (hb : b ∈ lambdaBranches y K J) :
    b.2.length ≤ 2*K := by
  simp only [lambdaBranches,List.mem_flatMap,List.mem_map] at hb
  obtain ⟨j,hj,c,hc,rfl⟩ := hb
  change c.2.length ≤ _
  rw [weighted_length _ J c hc,factors_length]
  have hj := List.mem_range.mp hj
  omega

theorem branches_length (y K : ℕ) (js : List ℕ) (b : Branch)
    (hb : b ∈ branches y K js) : b.2.length ≤ (js.length+1)*(2*K) := by
  induction js generalizing b with
  | nil => simpa using mu_length y K b hb
  | cons J js ih =>
    simp only [branches,multiply,List.mem_flatMap,List.mem_map] at hb
    obtain ⟨c,hc,e,he,rfl⟩ := hb
    have h1 := ih c hc
    have h2 := lambda_length y K J e he
    simp only [join,List.length_append,List.length_cons]
    nlinarith

#print axioms branches_length
#print axioms weighted_degrees
#print axioms branches_degrees
#print axioms branch_large_free_degrees
end XiPrime8845.PRZZBranchDegrees

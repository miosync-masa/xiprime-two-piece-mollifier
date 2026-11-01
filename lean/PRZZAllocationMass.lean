import PRZZDyadicBudget
import PRZZCoefficientSeparation

/-! Absolute scalar mass of all labelled allocations and all local HB
factor grids, including the two outer dyadic coordinates. Repeated list
entries are counted separately. Constants do not depend on local cutoffs. -/
noncomputable section
open scoped BigOperators
namespace XiPrime8845.PRZZAllocationMass
open PRZZHBBranches
set_option maxHeartbeats 2000000

def gridMass (N y K : ℕ) (js : List ℕ) : ℝ :=
  ((branches y K js).map (fun b =>
    |b.1| * (Nat.log 2 N+1:ℝ)^(b.2.length+2))).sum

theorem grid_mass (K : ℕ) (js : List ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ N y : ℕ, 1 ≤ N → ∀ T : ℝ,
      (N:ℝ) ≤ T → 1 ≤ Real.log T → gridMass N y K js ≤ C*T^eta := by
  obtain ⟨D,hD,hd⟩ := PRZZDyadicBudget.grids_absorbed ((js.length+1)*(2*K)+2) eta heta
  have hm := PRZZBranchMass.mass_nonneg K js
  refine ⟨PRZZBranchMass.mass K js*D+1,by positivity,?_⟩
  intro N y hN T hNT hL
  have hf (b : Branch) (hb : b ∈ branches y K js) :
      (Nat.log 2 N+1:ℝ)^(b.2.length+2) ≤ D*T^eta :=
    hd N hN T hNT hL _ (by have := PRZZBranchDegrees.branches_length y K js b hb; omega)
  have hsum (bs : List Branch) (hs : ∀ b ∈ bs, b ∈ branches y K js) :
      (bs.map (fun b => |b.1| * (Nat.log 2 N+1:ℝ)^(b.2.length+2))).sum ≤
      (bs.map (fun b => |b.1|)).sum*(D*T^eta) := by
    induction bs with
    | nil => simp
    | cons b bs ih =>
      simp only [List.map_cons,List.sum_cons,add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (hf b (hs b (by simp))) (abs_nonneg _))
        (ih (fun c hc => hs c (by simp [hc])))
  have hh := hsum (branches y K js) (fun b hb => hb)
  rw [PRZZBranchMass.mass_eq] at hh
  have ht : 0 ≤ T^eta := Real.rpow_nonneg (by linarith [show (0:ℝ) ≤ N from Nat.cast_nonneg N]) _
  exact hh.trans (by nlinarith)

/-- Even when every labelled allocation uses a different local root
cutoff, its full branch/grid multiplicity is a single subpower cost. -/
theorem allocation_mass (K : ℕ) (js : List ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ T : ℝ,
      (N:ℝ) ≤ T → 1 ≤ Real.log T →
      ∀ y : List ℕ × List ℕ → ℕ,
      ((PRZZCoefficientSeparation.allocations js).map (fun q =>
        gridMass N (y q) K q.2)).sum ≤ C*T^eta := by
  choose c hc hb using fun q : List ℕ × List ℕ => grid_mass K q.2 eta heta
  have hnon : 0 ≤ ((PRZZCoefficientSeparation.allocations js).map c).sum := by
    apply List.sum_nonneg
    intro a ha
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
    exact (hc q).le
  refine ⟨((PRZZCoefficientSeparation.allocations js).map c).sum+1,by linarith,?_⟩
  intro N hN T hNT hL y
  have hsum (qs : List (List ℕ × List ℕ)) :
      (qs.map (fun q => gridMass N (y q) K q.2)).sum ≤ (qs.map c).sum*T^eta := by
    induction qs with
    | nil => simp
    | cons q qs ih =>
      simp only [List.map_cons,List.sum_cons,add_mul]
      exact add_le_add (hb q N (y q) hN T hNT hL) ih
  have ht : 0 ≤ T^eta := Real.rpow_nonneg (by linarith [show (0:ℝ) ≤ N from Nat.cast_nonneg N]) _
  exact (hsum _).trans (by nlinarith)

#print axioms grid_mass
#print axioms allocation_mass
end XiPrime8845.PRZZAllocationMass

import PRZZHiAllocatedCells
import PRZZDyadicModulus
import PRZZLengthBudget

/-! Every original signed frequency is transferred to the signed source
cell consumed by the dyadic DI bound. Labelled HB branches and all grids
remain in their original lists, so repeated branches are not discarded. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZActualSignedBranches
open PRZZAStarNu PRZZNuCoefficient PRZZHBBranches PRZZActualBranchCells
set_option maxHeartbeats 2000000

def frequencyBound (d : ℕ) (D H : ℝ) : ℕ := ⌈D/d⌉.natAbs*⌊H⌋₊

theorem nu_zero (s : Finset (ℤ × ℕ)) (x y : ℝ) (v : ℤ)
    (hv : v ∉ s.image freq) : nu s x y v = 0 := by
  unfold nu
  apply sum_eq_zero
  intro q hq
  exact False.elim (hv (mem_image.mpr ⟨q,(mem_filter.mp hq).1,(mem_filter.mp hq).2⟩))

/-- This is an equality, not a triangle inequality over frequencies.
Both phase signs and every frequency-fiber multiplicity are preserved. -/
theorem frequency_pair (d : ℕ) (D H x y : ℝ) (F : ℤ → ℂ) :
    (∑ v ∈ (frequencies d D H).image freq, nu (frequencies d D H) x y v*F v) =
      (∑ a ∈ Icc 1 (frequencyBound d D H), nu (frequencies d D H) x y (a:ℤ)*F a)+
      (∑ a ∈ Icc 1 (frequencyBound d D H), nu (frequencies d D H) x y (-(a:ℤ))*F (-a)) := by
  classical
  let p := (Icc 1 (frequencyBound d D H)).image (fun a : ℕ => (a:ℤ))
  let n := (Icc 1 (frequencyBound d D H)).image (fun a : ℕ => -(a:ℤ))
  have hsub : (frequencies d D H).image freq ⊆ p ∪ n := by
    intro v hv
    have hh := PRZZLengthBudget.source_range d D H v hv
    have ha : v.natAbs ∈ Icc 1 (frequencyBound d D H) :=
      mem_Icc.mpr ⟨Int.natAbs_pos.mpr hh.1,hh.2⟩
    rcases le_total 0 v with h | h
    · exact mem_union_left _ (mem_image.mpr ⟨v.natAbs,ha,by omega⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨v.natAbs,ha,by omega⟩)
  have hdis : Disjoint p n := by
    apply disjoint_left.mpr
    intro v hv hn
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hv
    obtain ⟨b,hb,he⟩ := mem_image.mp hn
    have := (mem_Icc.mp ha).1
    have := (mem_Icc.mp hb).1
    omega
  rw [sum_subset hsub (fun v _ hv => by rw [nu_zero _ _ _ _ hv,zero_mul]),sum_union hdis]
  congr 1
  · rw [sum_image]
    intro a ha b hb he
    change (a:ℤ) = (b:ℤ) at he
    exact_mod_cast he
  · rw [sum_image]
    intro a ha b hb he
    have := neg_injective he
    exact_mod_cast this

theorem sum_list {ι α : Type*} (s : Finset ι) (bs : List α)
    (c : ι → ℂ) (f : ι → α → ℂ) :
    (∑ v ∈ s, c v*(bs.map (f v)).sum) =
      (bs.map (fun b => ∑ v ∈ s, c v*f v b)).sum := by
  induction bs with
  | nil => simp
  | cons b bs ih => simpa only [List.map_cons,List.sum_cons,mul_add,sum_add_distrib] using congrArg (fun z => (∑ v ∈ s, c v*f v b)+z) ih

/-- All scalar branch weights are outside the signed source cell. The
local HB root cutoff is the original row hi, not a substitute cutoff. -/
theorem cells_eq_sources (N d h j l K : ℕ) (ks js : List ℕ)
    (D H x y t : ℝ) (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) :
    (∑ v ∈ (frequencies d D H).image freq, nu (frequencies d D H) x y v*
      PRZZHiAllocatedCells.cells N d h j K ks
        (PRZZSupportedBranches.row N d j l (fun _ => 1)
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) F1 F2 FM alpha beta x t v)) =
      ((branches ⌊(PRZZRowWindow.hi N d h j:ℝ)^((K:ℝ)⁻¹)⌋₊ K ks).map
        (fun b => (b.1:ℂ)*∑ k : Fin b.2.length → Fin (Nat.log 2 N+1),
          PRZZSignedSourceCell.source N d j l h (frequencyBound d D H) b (fun i => (k i).val)
            (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) F1 F2 FM alpha beta x t
            (fun a => nu (frequencies d D H) x y (a:ℤ))
            (fun a => nu (frequencies d D H) x y (-(a:ℤ))))).sum := by
  unfold PRZZHiAllocatedCells.cells
  rw [sum_list]
  congr 1
  apply List.map_congr_left
  intro b hb
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  simp only [← mul_sum]
  rw [frequency_pair]
  unfold PRZZSignedSourceCell.source
  simp only [Nat.floor_natCast,mul_add,mul_sum]
  congr 1 <;> apply sum_congr rfl <;> intro a ha <;> apply sum_congr rfl <;> intro n hn <;>
    split_ifs <;> ring

#print axioms nu_zero
#print axioms frequency_pair
#print axioms sum_list
#print axioms cells_eq_sources
end XiPrime8845.PRZZActualSignedBranches

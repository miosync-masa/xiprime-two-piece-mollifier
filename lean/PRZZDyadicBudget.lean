import PRZZBranchMass
import PRZZSourceAbsorption
import PRZZDyadicSupport

/-! Count the full dyadic grids, not just selected balanced cells.
Fixed factor-count powers of log T are absorbed uniformly for N<=T.
Support-box inflation remains an explicit fixed factor 2^L. -/
noncomputable section
open scoped BigOperators
namespace XiPrime8845.PRZZDyadicBudget
set_option maxHeartbeats 2000000

theorem cell_count (N : ℕ) (T : ℝ) (hN : 1 ≤ N) (hNT : (N:ℝ) ≤ T)
    (hL : 1 ≤ Real.log T) :
    (Nat.log 2 N+1:ℝ) ≤ (1/Real.log 2+1)*Real.log T := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : (2:ℝ)^(Nat.log 2 N) ≤ N := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
  have hh := Real.log_le_log (pow_pos (by norm_num : (0:ℝ)<2) _) hp
  rw [Real.log_pow] at hh
  have hlog := Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) hNT
  have hb : (Nat.log 2 N:ℝ) ≤ Real.log T/Real.log 2 :=
    (le_div_iff₀ h2).mpr (hh.trans hlog)
  have he : (1/Real.log 2+1)*Real.log T = Real.log T/Real.log 2+Real.log T := by ring
  rw [he]
  linarith

theorem grids_absorbed (L : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ T : ℝ,
      (N:ℝ) ≤ T → 1 ≤ Real.log T → ∀ m ≤ L,
        ((Nat.log 2 N+1:ℝ)^m) ≤ C*T^eta := by
  obtain ⟨D,hD,hd⟩ := PRZZGAbsorption.log_pow_bound L eta heta
  let a := 1/Real.log 2+1
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a^L*D,by positivity,?_⟩
  intro N hN T hNT hL m hm
  have hT : 1 ≤ T := (by exact_mod_cast hN : (1:ℝ) ≤ N).trans hNT
  have hc : (1:ℝ) ≤ Nat.log 2 N+1 := by have := Nat.cast_nonneg (α := ℝ) (Nat.log 2 N); linarith
  calc
    _ ≤ (Nat.log 2 N+1:ℝ)^L := pow_le_pow_right₀ hc hm
    _ ≤ (a*Real.log T)^L := pow_le_pow_left₀ (by positivity) (cell_count N T hN hNT hL) L
    _ = a^L*(Real.log T)^L := mul_pow _ _ _
    _ ≤ a^L*(D*T^eta) := mul_le_mul_of_nonneg_left (hd T hT) (pow_nonneg ha.le _)
    _ = _ := by ring

/-- Full assignments of a dyadic cell to every factor, before pruning. -/
theorem grid_card (N m : ℕ) :
    Fintype.card (Fin m → Fin (Nat.log 2 N+1)) = (Nat.log 2 N+1)^m := by simp

theorem support_inflation (L : ℕ) (ks : List ℕ) (hk : ks.length ≤ L) :
    2^(ks.sum+ks.length) ≤ 2^L*2^ks.sum := by
  rw [pow_add,mul_comm (2^L)]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hk)

/-- Both branch-factor grids and the two outer dyadic coordinates fit in
one height-uniform budget, including all absolute scalar branch weights. -/
theorem branch_pair_grids (K : ℕ) (js : List ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ y b c,
      b ∈ PRZZHBBranches.branches y K js → c ∈ PRZZHBBranches.branches y K js →
      ∀ N : ℕ, 1 ≤ N → ∀ T : ℝ, (N:ℝ) ≤ T → 1 ≤ Real.log T →
      (PRZZBranchMass.mass K js)^2*(Nat.log 2 N+1:ℝ)^(b.2.length+c.2.length+2) ≤ C*T^eta := by
  obtain ⟨D,hD,hd⟩ := grids_absorbed (2*((js.length+1)*(2*K))+2) eta heta
  refine ⟨(PRZZBranchMass.mass K js)^2*D+1,by positivity,?_⟩
  intro y b c hb hc N hN T hNT hL
  have hbL := PRZZBranchDegrees.branches_length y K js b hb
  have hcL := PRZZBranchDegrees.branches_length y K js c hc
  have h := mul_le_mul_of_nonneg_left
    (hd N hN T hNT hL (b.2.length+c.2.length+2) (by omega)) (sq_nonneg (PRZZBranchMass.mass K js))
  apply h.trans
  have ht : 0 ≤ T^eta := Real.rpow_nonneg
    ((by exact_mod_cast (show 0 ≤ N from Nat.zero_le N) : (0:ℝ) ≤ N).trans hNT) _
  nlinarith

#print axioms branch_pair_grids
#print axioms cell_count
#print axioms grids_absorbed
#print axioms grid_card
#print axioms support_inflation
end XiPrime8845.PRZZDyadicBudget

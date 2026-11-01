import PRZZCellMass

/-! A retained sample compares the actual local product U to a common
row scale X/h. X depends on the row and fixed HB length, not on the
chosen branch or factor grid. No asymptotic comparison is assumed. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZRetainedScale
open PRZZActualBranchCells PRZZHBBranches
set_option maxHeartbeats 2000000

theorem retained_scale (N d h j y K : ℕ) (ks : List ℕ)
    (hd : 0 < d) (hh : 0 < h) (b : Branch) (hb : b ∈ branches y K ks)
    (k : Fin b.2.length → ℕ) (U : ℝ) (hp : ∏ a, (2:ℝ)^(k a) = U)
    (n : ℕ) (hl : PRZZRowWindow.lo h j ≤ n) (hu : n ≤ PRZZRowWindow.hi N d h j)
    (hz : group N b k univ n ≠ 0) :
    let c : ℝ := 2^((ks.length+1)*(2*K))
    let X : ℝ := (2:ℝ)^j/c
    X/h ≤ U ∧ U ≤ (2*c)*(X/h) := by
  dsimp only
  let c : ℝ := 2^((ks.length+1)*(2*K))
  have hc : 0 < c := by dsimp [c]; positivity
  have hhR : (0:ℝ) < h := by exact_mod_cast hh
  have hm := (PRZZRowWindow.test N d h j n hd hh).mpr ⟨hl,hu⟩
  rw [PRZZDyadic.mem_cell] at hm
  have hlo : (2:ℝ)^j ≤ (h:ℝ)*n := by exact_mod_cast hm.1.2.1
  have hhi : (h:ℝ)*n ≤ (2:ℝ)^(j+1) := by exact_mod_cast hm.1.2.2.le
  have hg := group_support N b k univ n hz
  have hUn : U ≤ (n:ℝ) := by
    rw [← hp]
    exact_mod_cast hg.1
  have hnU : (n:ℝ) ≤ c*U := by
    apply (show (n:ℝ) ≤ ∏ a ∈ univ, (2:ℝ)^(k a+1) by exact_mod_cast hg.2).trans
    exact PRZZCellMass.upper_support y K ks b hb k univ U hp.le
  change ((2:ℝ)^j/c)/h ≤ U ∧ U ≤ (2*c)*(((2:ℝ)^j/c)/h)
  constructor
  · apply (div_le_iff₀ hhR).mpr
    apply (div_le_iff₀ hc).mpr
    nlinarith [mul_le_mul_of_nonneg_left hnU hhR.le]
  · have hhU : U ≤ (2:ℝ)^(j+1)/h :=
      (le_div_iff₀ hhR).mpr (by nlinarith [mul_le_mul_of_nonneg_left hUn hhR.le])
    apply hhU.trans_eq
    rw [pow_succ]
    field_simp
    <;> ring

#print axioms retained_scale

/-- Transfer the classifier's balanced boxes to the common row scale.
The inflation is fixed by HB length; it does not grow with h or height. -/
theorem balanced_boxes (Z U E Y c : ℝ) (hZ : 0 ≤ Z) (hc : 1 ≤ c)
    (hlo : Z ≤ U) (hhi : U ≤ (2*c)*Z)
    (hElo : U^(1/4:ℝ) ≤ E) (hEhi : E ≤ c*U^(1/2:ℝ))
    (hY : Y ≤ c*U) :
    Z^(1/4:ℝ) ≤ E ∧ E ≤ (2*c^2)*Z^(1/2:ℝ) ∧ Y ≤ (2*c^2)*Z := by
  have hc0 : 0 ≤ c := by linarith
  have hp : (2*c)^(1/2:ℝ) ≤ 2*c := by
    simpa using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ 2*c by linarith)
      (show (1/2:ℝ) ≤ 1 by norm_num)
  refine ⟨(Real.rpow_le_rpow hZ hlo (by norm_num)).trans hElo,?_,?_⟩
  · calc
      E ≤ c*((2*c)*Z)^(1/2:ℝ) := hEhi.trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hZ.trans hlo) hhi (by norm_num)) hc0)
      _ = c*((2*c)^(1/2:ℝ)*Z^(1/2:ℝ)) := by rw [Real.mul_rpow (by positivity) hZ]
      _ ≤ c*((2*c)*Z^(1/2:ℝ)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hZ _)) hc0
      _ = _ := by ring
  · exact hY.trans ((mul_le_mul_of_nonneg_left hhi hc0).trans_eq (by ring))

#print axioms balanced_boxes
end XiPrime8845.PRZZRetainedScale

import PRZZFreeLengthCoefficient

/-! Effective Type I endpoint in the actual signed HB cell. The
complementary convolution mass is retained; no DI/seven-term comparison
or final h/outer integral estimate is asserted here. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZFreeLengthCell
open PRZZActualBranchCells PRZZHBBranches PRZZFreeCoefficient
open PRZZFreeLength PRZZFreeLengthCoefficient
set_option maxHeartbeats 3000000

/-- Uniform constants precede the branch, cutoff, grouping and height. -/
theorem signed_cell_bound (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM)
    (K : ℕ) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ N y d j l h : ℕ, ∀ b ∈ branches y K ks,
      ∀ k : Fin b.2.length → ℕ, ∀ i : Fin b.2.length,
      group N b k univ ≠ 0 → (y:ℝ) < (2:ℝ)^(k i) →
      ∀ T Q x y0 t D H L : ℝ, ∀ alpha beta : ℂ,
      0 < N → 0 < d → 0 < h → 1 ≤ L →
      (∏ a ∈ univ.erase i, (2:ℝ)^(k a+1)) ≤ L →
      1 < T → (N:ℝ)+1 ≤ T → |alpha.re| ≤ S/Real.log T →
      1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T →
      ‖∑ v ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
        PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y0 v *
          PRZZFreeCell.cell N d j l h b k js F0 F2 FM Q x t alpha beta v‖ ≤
        C*L^eta*L*(1+|t|)*(T^eta*T^eta)*
          ∑ v ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
            (v.natAbs:ℝ)^eta*budget eps N d l (endpoint N d h 1 (k i)) v := by
  obtain ⟨Cs,hCs,hs⟩ := PRZZFreeLengthCoefficient.signed_slice_bound hWeil F0 F2 FM hf hc hF hcF hM hcM
    js (ks.sum+1) eps eta S Z heps heta hS hZ
  obtain ⟨Cg,hCg,hg⟩ := PRZZCellMass.weighted_mass K ks eta heta
  refine ⟨Cg*Cs,mul_pos hCg hCs,?_⟩
  intro N y d j l h b hb k i hn hi T Q x y0 t D H L alpha beta hN hd hh hL hsup
    hT hNT ha hz hbeta
  obtain ⟨m,hm,hp⟩ := PRZZBareFactors.large_piece N y K ks b hb k i hn hi
  simp_rw [PRZZFreeCell.cell,PRZZFreeCell.cell_eq N d j l h hd hh b k i m hp js F0 F2 FM Q x t alpha beta]
  simp only [mul_sum]
  rw [sum_comm]
  have heq : (∑ e ∈ Icc 1 N,
      ∑ v ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
        PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y0 v *
          ((group N b k (univ.erase i) e:ℂ) *
            slice N d j l h e (k i) m js F0 F2 FM Q x t alpha beta v)) =
      ∑ e ∈ Icc 1 N, (group N b k (univ.erase i) e:ℂ) *
        ∑ v ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
          PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y0 v *
            slice N d j l h e (k i) m js F0 F2 FM Q x t alpha beta v := by
    simp only [mul_sum]; apply sum_congr rfl; intro e he
    apply sum_congr rfl; intro v hv; ring
  rw [heq]
  have hbudget : 0 ≤ ∑ v ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
      (v.natAbs:ℝ)^eta*budget eps N d l (endpoint N d h 1 (k i)) v :=
    sum_nonneg (fun v _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (budget_nonneg eps N d l (endpoint N d h 1 (k i)) v))
  apply (hg N y b hb k (univ.erase i) L
    (Cs*(1+|t|)*(T^eta*T^eta)*
      ∑ v ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
        (v.natAbs:ℝ)^eta*budget eps N d l (endpoint N d h 1 (k i)) v)
    hL (by positivity) hsup _ ?_).trans_eq
  · simp only [mul_sum]
    apply sum_congr rfl
    intro v hv
    ring
  · intro e he
    apply (hs N d j l h e (k i) m T Q x y0 t D H alpha beta hN hd hh
      (mem_Icc.mp he).1 hm hT hNT ha hz hbeta).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply sum_le_sum
    intro v hv
    exact mul_le_mul_of_nonneg_left
      (budget_mono eps N d l _ _ v (endpoint_le N d h e (k i) hd hh (mem_Icc.mp he).1))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)


#print axioms signed_cell_bound
end XiPrime8845.PRZZFreeLengthCell

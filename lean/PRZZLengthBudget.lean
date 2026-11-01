import PRZZFreeLengthCell

/-! Frequency gcd averaging with an independent effective free endpoint.
The modulus dyadic cell still uses the original N. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZLengthBudget
open PRZZFreeLengthCoefficient
open PRZZModulusBudget (weighted_gcd)
set_option maxHeartbeats 2000000

def averaged (eps : ℝ) (N d l M : ℕ) : ℝ :=
  ∑ q ∈ PRZZDyadic.cell N l,
    Real.rpow q (1/2+eps)*(d.divisors.card:ℝ)*(1+(M:ℝ)/q)*(q.divisors.card:ℝ)

theorem positive_budget (eps eta : ℝ) (heta : 0 ≤ eta) (N d l M A : ℕ) :
    (∑ a ∈ Icc 1 A, (a:ℝ)^eta*budget eps N d l M a) ≤
      (A:ℝ)^eta*(A:ℝ)*averaged eps N d l M := by
  unfold budget
  simp only [mul_sum,Int.natAbs_natCast]
  rw [sum_comm]
  unfold averaged
  rw [mul_sum]
  apply sum_le_sum
  intro q hq
  let B := Real.rpow q (1/2+eps)*(d.divisors.card:ℝ)*(1+(M:ℝ)/q)
  have hB : 0 ≤ B := by
    have hp := Real.rpow_nonneg (Nat.cast_nonneg q) (1/2+eps)
    dsimp [B]; positivity
  have he : (∑ a ∈ Icc 1 A,
      (a:ℝ)^eta*(Real.rpow q (1/2+eps)*(d.divisors.card:ℝ)*(a.gcd q:ℝ)*(1+(M:ℝ)/q))) =
      B*∑ a ∈ Icc 1 A, (a:ℝ)^eta*(a.gcd q:ℝ) := by
    rw [mul_sum]; apply sum_congr rfl; intros; dsimp [B]; ring
  rw [he]
  exact (mul_le_mul_of_nonneg_left (weighted_gcd A q
    (by have := (mem_Icc.mp (mem_filter.mp hq).1).1; omega) eta heta) hB).trans_eq
      (by dsimp [B]; ring)

theorem signed_budget (eps eta : ℝ) (heta : 0 ≤ eta) (N d l M A : ℕ)
    (s : Finset ℤ) (hs : ∀ k ∈ s, k ≠ 0 ∧ k.natAbs ≤ A) :
    (∑ k ∈ s, (k.natAbs:ℝ)^eta*budget eps N d l M k) ≤
      2*(A:ℝ)^eta*(A:ℝ)*averaged eps N d l M := by
  classical
  let p := (Icc 1 A).image (fun a : ℕ => (a:ℤ))
  let n := (Icc 1 A).image (fun a : ℕ => -(a:ℤ))
  have hsub : s ⊆ p ∪ n := by
    intro k hk
    have hka : k.natAbs ∈ Icc 1 A := mem_Icc.mpr
      ⟨Int.natAbs_pos.mpr (hs k hk).1,(hs k hk).2⟩
    rcases le_total 0 k with h | h
    · exact mem_union_left _ (mem_image.mpr ⟨k.natAbs,hka,by omega⟩)
    · apply mem_union_right
      exact mem_image.mpr ⟨k.natAbs,hka,by omega⟩
  have hdis : Disjoint p n := by
    apply disjoint_left.mpr
    intro k hk hn
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hk
    obtain ⟨b,hb,he⟩ := mem_image.mp hn
    have := (mem_Icc.mp ha).1
    have := (mem_Icc.mp hb).1
    omega
  apply (sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ =>
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (budget_nonneg eps N d l M k))).trans
  rw [sum_union hdis]
  have hp : (∑ k ∈ p, (k.natAbs:ℝ)^eta*budget eps N d l M k) =
      ∑ a ∈ Icc 1 A, (a:ℝ)^eta*budget eps N d l M a := by
    rw [sum_image]
    · simp only [Int.natAbs_natCast]
    · intro a ha b hb he; change (a:ℤ) = (b:ℤ) at he; omega
  have hn : (∑ k ∈ n, (k.natAbs:ℝ)^eta*budget eps N d l M k) =
      ∑ a ∈ Icc 1 A, (a:ℝ)^eta*budget eps N d l M a := by
    rw [sum_image]
    · simp only [Int.natAbs_neg,Int.natAbs_natCast,budget]
    · intro a ha b hb he; have := neg_injective he; exact_mod_cast this
  rw [hp,hn]
  have h := positive_budget eps eta heta N d l M A
  linarith

theorem source_range (d : ℕ) (D H : ℝ) :
    ∀ k ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
      k ≠ 0 ∧ k.natAbs ≤ ⌈D/d⌉.natAbs*⌊H⌋₊ := by
  intro k hk
  refine ⟨PRZZAStarNu.frequency_ne_zero d D H k hk,?_⟩
  obtain ⟨q,hq,rfl⟩ := mem_image.mp hk
  have hq1 := mem_Icc.mp (mem_filter.mp (mem_product.mp hq).1).1
  have hq2 := mem_Icc.mp (mem_filter.mp (mem_product.mp hq).2).1
  have hdelta : q.1.natAbs ≤ ⌈D/d⌉.natAbs := by omega
  simp only [PRZZNuCoefficient.freq,Int.natAbs_mul,Int.natAbs_natCast]
  exact (Nat.mul_le_mul hq2.2 hdelta).trans_eq (Nat.mul_comm _ _)

theorem source_budget (eps eta : ℝ) (heta : 0 ≤ eta) (N d l M : ℕ) (D H : ℝ) :
    (∑ k ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
      (k.natAbs:ℝ)^eta*budget eps N d l M k) ≤
      2*((⌈D/d⌉.natAbs*⌊H⌋₊:ℕ):ℝ)^eta*((⌈D/d⌉.natAbs*⌊H⌋₊:ℕ):ℝ)*
        averaged eps N d l M :=
  signed_budget eps eta heta N d l M _ _ (source_range d D H)


#print axioms positive_budget
#print axioms signed_budget
#print axioms source_range
#print axioms source_budget
open PRZZActualBranchCells PRZZHBBranches PRZZFreeLength

theorem signed_cell_averaged (hWeil : PRZZKloostermanInputs.WeilIncomplete)
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
          (2*((⌈D/d⌉.natAbs*⌊H⌋₊:ℕ):ℝ)^eta*((⌈D/d⌉.natAbs*⌊H⌋₊:ℕ):ℝ)*
            averaged eps N d l (endpoint N d h 1 (k i))) := by
  obtain ⟨C,hC,hbound⟩ := PRZZFreeLengthCell.signed_cell_bound hWeil F0 F2 FM
    hf hc hF hcF hM hcM K ks js eps eta S Z heps heta hS hZ
  refine ⟨C,hC,?_⟩
  intro N y d j l h b hb k i hn hi T Q x y0 t D H L alpha beta hN hd hh hL hsup hT hNT ha hz hbeta
  apply (hbound N y d j l h b hb k i hn hi T Q x y0 t D H L alpha beta
    hN hd hh hL hsup hT hNT ha hz hbeta).trans
  exact mul_le_mul_of_nonneg_left (source_budget eps eta heta.le N d l _ D H)
    (by positivity)

#print axioms signed_cell_averaged

end XiPrime8845.PRZZLengthBudget

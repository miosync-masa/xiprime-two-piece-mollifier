import PRZZFreeCell

/-! Average the gcd before the modulus sum. Both signs and every
frequency of the original strict source cutoff are retained. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZModulusBudget
open PRZZFreeCoefficient
set_option maxHeartbeats 2000000

theorem weighted_gcd (A q : ℕ) (hq : q ≠ 0) (eta : ℝ) (heta : 0 ≤ eta) :
    (∑ a ∈ Icc 1 A, (a:ℝ)^eta*(a.gcd q:ℝ)) ≤
      (A:ℝ)^eta*(A:ℝ)*q.divisors.card := by
  calc
    _ ≤ ∑ a ∈ Icc 1 A, (A:ℝ)^eta*(a.gcd q:ℝ) := by
      apply sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (mem_Icc.mp ha).2) heta)
        (Nat.cast_nonneg _)
    _ = (A:ℝ)^eta*∑ a ∈ Icc 1 A, (a.gcd q:ℝ) := by rw [mul_sum]
    _ ≤ _ := (mul_le_mul_of_nonneg_left
      (PRZZTypeIFrequency.gcd_sum_real A q hq) (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans_eq (by ring)

def averaged (eps : ℝ) (N d l : ℕ) : ℝ :=
  ∑ q ∈ PRZZDyadic.cell N l,
    Real.rpow q (1/2+eps)*(d.divisors.card:ℝ)*(1+(N:ℝ)/q)*(q.divisors.card:ℝ)

theorem positive_budget (eps eta : ℝ) (heta : 0 ≤ eta) (N d l A : ℕ) :
    (∑ a ∈ Icc 1 A, (a:ℝ)^eta*modulusBudget eps N d l a) ≤
      (A:ℝ)^eta*(A:ℝ)*averaged eps N d l := by
  unfold modulusBudget
  simp only [mul_sum,Int.natAbs_natCast]
  rw [sum_comm]
  unfold averaged
  rw [mul_sum]
  apply sum_le_sum
  intro q hq
  let B := Real.rpow q (1/2+eps)*(d.divisors.card:ℝ)*(1+(N:ℝ)/q)
  have hB : 0 ≤ B := by
    have hp := Real.rpow_nonneg (Nat.cast_nonneg q) (1/2+eps)
    dsimp [B]; positivity
  have he : (∑ a ∈ Icc 1 A,
      (a:ℝ)^eta*(Real.rpow q (1/2+eps)*(d.divisors.card:ℝ)*(a.gcd q:ℝ)*(1+(N:ℝ)/q))) =
      B*∑ a ∈ Icc 1 A, (a:ℝ)^eta*(a.gcd q:ℝ) := by
    rw [mul_sum]; apply sum_congr rfl; intros; dsimp [B]; ring
  rw [he]
  exact (mul_le_mul_of_nonneg_left (weighted_gcd A q
    (by have := (mem_Icc.mp (mem_filter.mp hq).1).1; omega) eta heta) hB).trans_eq
      (by dsimp [B]; ring)

theorem signed_budget (eps eta : ℝ) (heta : 0 ≤ eta) (N d l A : ℕ)
    (s : Finset ℤ) (hs : ∀ k ∈ s, k ≠ 0 ∧ k.natAbs ≤ A) :
    (∑ k ∈ s, (k.natAbs:ℝ)^eta*modulusBudget eps N d l k) ≤
      2*(A:ℝ)^eta*(A:ℝ)*averaged eps N d l := by
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
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (modulusBudget_nonneg eps N d l k))).trans
  rw [sum_union hdis]
  have hp : (∑ k ∈ p, (k.natAbs:ℝ)^eta*modulusBudget eps N d l k) =
      ∑ a ∈ Icc 1 A, (a:ℝ)^eta*modulusBudget eps N d l a := by
    rw [sum_image]
    · simp only [Int.natAbs_natCast]
    · intro a ha b hb he; change (a:ℤ) = (b:ℤ) at he; omega
  have hn : (∑ k ∈ n, (k.natAbs:ℝ)^eta*modulusBudget eps N d l k) =
      ∑ a ∈ Icc 1 A, (a:ℝ)^eta*modulusBudget eps N d l a := by
    rw [sum_image]
    · simp only [Int.natAbs_neg,Int.natAbs_natCast,modulusBudget]
    · intro a ha b hb he; have := neg_injective he; exact_mod_cast this
  rw [hp,hn]
  have h := positive_budget eps eta heta N d l A
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

theorem source_budget (eps eta : ℝ) (heta : 0 ≤ eta) (N d l : ℕ) (D H : ℝ) :
    (∑ k ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
      (k.natAbs:ℝ)^eta*modulusBudget eps N d l k) ≤
      2*((⌈D/d⌉.natAbs*⌊H⌋₊:ℕ):ℝ)^eta*((⌈D/d⌉.natAbs*⌊H⌋₊:ℕ):ℝ)*
        averaged eps N d l :=
  signed_budget eps eta heta N d l _ _ (source_range d D H)

/-- The two divisor costs are absorbed uniformly before summing moduli.
The remaining length/modulus cost is retained literally. -/
theorem averaged_absorbed (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d l : ℕ, ∀ T eps : ℝ,
      0 < d → (d:ℝ) ≤ T → (N:ℝ) ≤ T →
      averaged eps N d l ≤ C*T^eta*
        ∑ q ∈ PRZZDyadic.cell N l, Real.rpow q (1/2+eps)*(1+(N:ℝ)/q) := by
  obtain ⟨C,hC,h⟩ := PRZZTypeICost.divisor_pair_absorbed eta heta
  refine ⟨C,hC,?_⟩
  intro N d l T eps hd hdT hNT
  unfold averaged
  rw [mul_sum]
  apply sum_le_sum
  intro q hq
  have hqn := mem_Icc.mp (mem_filter.mp hq).1
  have hb := h d q hd (by omega) T hdT
    ((by exact_mod_cast hqn.2 : (q:ℝ) ≤ N).trans hNT)
  have hp : 0 ≤ Real.rpow (q:ℝ) (1/2+eps)*(1+(N:ℝ)/q) :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
  convert mul_le_mul_of_nonneg_left hb hp using 1 <;> ring

open PRZZActualBranchCells PRZZHBBranches

/-- Actual Type I cells, including nu and the complementary coefficient,
now have no unaveraged frequency gcd. This does not yet assert a seven-term
bound: the modulus sum and its original N/q cost remain explicit. -/
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
            averaged eps N d l) := by
  obtain ⟨C,hC,hbound⟩ := PRZZFreeCell.signed_cell_bound hWeil F0 F2 FM
    hf hc hF hcF hM hcM K ks js eps eta S Z heps heta hS hZ
  refine ⟨C,hC,?_⟩
  intro N y d j l h b hb k i hn hi T Q x y0 t D H L alpha beta hN hd hh hL hsup hT hNT ha hz hbeta
  apply (hbound N y d j l h b hb k i hn hi T Q x y0 t D H L alpha beta
    hN hd hh hL hsup hT hNT ha hz hbeta).trans
  exact mul_le_mul_of_nonneg_left (source_budget eps eta heta.le N d l D H)
    (by positivity)

#print axioms weighted_gcd
#print axioms positive_budget
#print axioms signed_budget
#print axioms source_range
#print axioms source_budget
#print axioms averaged_absorbed
#print axioms signed_cell_averaged
end XiPrime8845.PRZZModulusBudget

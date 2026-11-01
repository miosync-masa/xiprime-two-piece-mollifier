import PRZZBareFactors
import PRZZFreeCoefficient
import PRZZCellMass

/-! The literal Type I cell is a sum of the analytic free slices, with
its actual complementary convolution coefficient retained. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset ArithmeticFunction
namespace XiPrime8845.PRZZFreeCell
open PRZZActualBranchCells PRZZHBBranches PRZZFreeCoefficient
set_option maxHeartbeats 3000000

theorem real_convolution (N : ℕ) (f g : ArithmeticFunction ℝ) (w : ℕ → ℂ) :
    (∑ n ∈ Icc 1 N, w n*((f*g) n:ℂ)) =
      ∑ e ∈ Icc 1 N, ∑ a ∈ Icc 1 N,
        if e*a ≤ N then w (e*a)*(f e:ℂ)*(g a:ℂ) else 0 := by
  simp only [mul_apply,Complex.ofReal_sum,Complex.ofReal_mul,mul_sum]
  trans ∑ n ∈ Icc 1 N,
    ∑ p ∈ (Icc 1 N ×ˢ Icc 1 N).filter (fun p => p.1*p.2=n),
      w n*((f p.1:ℂ)*(g p.2:ℂ))
  · apply sum_congr rfl
    intro n hn
    rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le
      (by have := (mem_Icc.mp hn).1; omega) (mem_Icc.mp hn).2]
    rfl
  · simp only [sum_filter]
    rw [sum_comm,Finset.sum_product]
    apply sum_congr rfl; intro e he
    apply sum_congr rfl; intro a ha
    have hp : 1 ≤ e*a := by nlinarith [(mem_Icc.mp he).1,(mem_Icc.mp ha).1]
    simp [mem_Icc,hp,mul_assoc]

/-- Freeze the complementary product e, preserving BOTH sharp cutoffs.
The redundant e*a<=N is removed only using d,h>=1 and the stronger
original d*h*e*a<=N condition. -/
theorem cell_eq (N d j l h : ℕ) (hd : 0 < d) (hh : 0 < h)
    (b : Branch) (k : Fin b.2.length → ℕ) (i : Fin b.2.length) (m : ℕ)
    (hp : ∀ a : ℕ, (piece N b k i a:ℂ) =
      if a ∈ PRZZDyadic.cell N (k i) then (Real.log a:ℂ)^m else 0)
    (js : List ℕ) (F0 F2 FM : ℝ → ℂ) (Q x t : ℝ) (alpha beta : ℂ) (v : ℤ) :
    (∑ n ∈ Icc 1 N, if d.Coprime n ∧ d*(h*n) ≤ N then
      (group N b k univ n:ℂ) *
        PRZZSupportedBranches.row N d j l (fun _ => 1)
          (fun a => (PRZZGCoefficient.coefficient js a:ℂ))
          (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha beta x t v (h*n)
      else 0) =
    ∑ e ∈ Icc 1 N, (group N b k (univ.erase i) e:ℂ) *
      slice N d j l h e (k i) m js F0 F2 FM Q x t alpha beta v := by
  classical
  let R := PRZZSupportedBranches.row N d j l (fun _ => 1)
    (fun a => (PRZZGCoefficient.coefficient js a:ℂ))
    (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha beta x t v
  let w := fun n => if d.Coprime n ∧ d*(h*n) ≤ N then R (h*n) else 0
  have hg : group N b k univ = group N b k (univ.erase i)*piece N b k i := by
    exact (prod_erase_mul _ _ (mem_univ i)).symm
  have heq : (∑ n ∈ Icc 1 N, if d.Coprime n ∧ d*(h*n) ≤ N then
      (group N b k univ n:ℂ)*R (h*n) else 0) =
      ∑ n ∈ Icc 1 N, w n*(group N b k univ n:ℂ) := by
    apply sum_congr rfl; intro n hn
    dsimp [w]; split_ifs <;> ring
  change (∑ n ∈ Icc 1 N, if d.Coprime n ∧ d*(h*n) ≤ N then
      (group N b k univ n:ℂ)*R (h*n) else 0) = _
  rw [heq,hg,real_convolution]
  apply sum_congr rfl
  intro e he
  rw [PRZZFreeCoefficient.slice,mul_sum]
  apply sum_congr rfl
  intro a ha
  rw [hp a]
  dsimp only [w,R]
  by_cases hcut : d.Coprime (e*a) ∧ d*(h*(e*a)) ≤ N
  · have hsmall : e*a ≤ N := by
      have ht := Nat.mul_le_mul_right (e*a) (Nat.mul_pos hd hh)
      have ht' : e*a ≤ d*(h*(e*a)) := by simpa [Nat.mul_assoc] using ht
      exact ht'.trans hcut.2
    simp only [if_pos hsmall,if_pos hcut]
    ring
  · by_cases hsmall : e*a ≤ N <;> simp [hcut,hsmall]

def cell (N d j l h : ℕ) (b : Branch) (k : Fin b.2.length → ℕ)
    (js : List ℕ) (F0 F2 FM : ℝ → ℂ) (Q x t : ℝ) (alpha beta : ℂ) (v : ℤ) : ℂ :=
  ∑ n ∈ Icc 1 N, if d.Coprime n ∧ d*(h*n) ≤ N then
    (group N b k univ n:ℂ) *
      PRZZSupportedBranches.row N d j l (fun _ => 1)
        (fun a => (PRZZGCoefficient.coefficient js a:ℂ))
        (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha beta x t v (h*n)
    else 0

/-- Sum every original signed frequency and the actual complementary
group. Its support length L is charged explicitly, not replaced by N.
Uniform constants precede the branch, cutoff, grouping and height. -/
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
          cell N d j l h b k js F0 F2 FM Q x t alpha beta v‖ ≤
        C*L^eta*L*(1+|t|)*(T^eta*T^eta)*
          ∑ v ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
            (v.natAbs:ℝ)^eta*modulusBudget eps N d l v := by
  obtain ⟨Cs,hCs,hs⟩ := signed_slice_bound hWeil F0 F2 FM hf hc hF hcF hM hcM
    js (ks.sum+1) eps eta S Z heps heta hS hZ
  obtain ⟨Cg,hCg,hg⟩ := PRZZCellMass.weighted_mass K ks eta heta
  refine ⟨Cg*Cs,mul_pos hCg hCs,?_⟩
  intro N y d j l h b hb k i hn hi T Q x y0 t D H L alpha beta hN hd hh hL hsup
    hT hNT ha hz hbeta
  obtain ⟨m,hm,hp⟩ := PRZZBareFactors.large_piece N y K ks b hb k i hn hi
  simp_rw [cell,cell_eq N d j l h hd hh b k i m hp js F0 F2 FM Q x t alpha beta]
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
      (v.natAbs:ℝ)^eta*modulusBudget eps N d l v :=
    sum_nonneg (fun v _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (modulusBudget_nonneg eps N d l v))
  apply (hg N y b hb k (univ.erase i) L
    (Cs*(1+|t|)*(T^eta*T^eta)*
      ∑ v ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
        (v.natAbs:ℝ)^eta*modulusBudget eps N d l v)
    hL (by positivity) hsup _ ?_).trans_eq
  · simp only [mul_sum]
    apply sum_congr rfl
    intro v hv
    ring
  · intro e he
    exact hs N d j l h e (k i) m T Q x y0 t D H alpha beta hN hd hh
      (mem_Icc.mp he).1 hm hT hNT ha hz hbeta

#print axioms signed_cell_bound
#print axioms real_convolution
#print axioms cell_eq
end XiPrime8845.PRZZFreeCell

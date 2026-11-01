import PRZZSupportedSplit
import PRZZLiteralBranches

/-! Exact supported h blocks of every actual HB branch pair. The inverse
residue, shifts, twists, smooth cutoffs and sharp d*h*r constraint remain
literal. This identity is not yet an identification with a balanced DI block. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory
namespace XiPrime8845.PRZZSupportedBranches
open PRZZSupportedSplit PRZZHBBranches PRZZHBRectangles
open PRZZAStarNu PRZZNuCoefficient PRZZMellinSeparation
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

def row (N d j l : ℕ) (a b : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ)
    (α β : ℂ) (x t : ℝ) (k : ℤ) (n1 : ℕ) : ℂ :=
  if n1 ∈ PRZZDyadic.cell N j then
    ∑ n2 ∈ PRZZDyadic.cell N l,
      if n1.Coprime n2 ∧ d*n2 ≤ N then
        (a (d*n1)*F1 (d*n1)/(n1:ℂ)^α*twist n1 t)*
        (star (b (d*n2))*F2 (d*n2)*FM (x*n2)/(n2:ℂ)^β*twist n2 t)*
        PRZZKloostermanInputs.e (-(k:ℝ)*PRZZKloostermanInputs.inverseResidue n2 n1/n2)
      else 0
  else 0

def block (N d j l : ℕ) (a b : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ)
    (α β : ℂ) (x t : ℝ) (k : ℤ) (h : ℕ) : ℂ :=
  ∑ r ∈ Icc 1 N, if d.Coprime r ∧ d*(h*r) ≤ N then
    row N d j l a b F1 F2 FM α β x t k (h*r) else 0

theorem mixed_row (N d j l : ℕ) (a b : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ)
    (α β : ℂ) (x t : ℝ) (k : ℤ) :
    mixed N d j l a b F1 F2 FM α β x t k =
      ∑ n ∈ Icc 1 N, if d*n ≤ N then row N d j l a b F1 F2 FM α β x t k n else 0 := by
  unfold mixed row
  simp only [PRZZDyadic.cell,sum_filter,mem_filter]
  apply sum_congr rfl
  intro n hn
  by_cases hj : Nat.log 2 n = j <;> by_cases hd : d*n ≤ N
  · simp only [hn,hj,hd,if_true,true_and,and_true]
  · simp [hd]
  · simp [hj,hn]
  · simp [hj,hd]

/-- Valid for arbitrary arithmetic coefficients, hence separately for
each actual branch without a multiplicativity assumption on that branch. -/
theorem mixed_supported (N d j l : ℕ) (hd : 1 ≤ d) (a b : ℕ → ℂ)
    (F1 F2 FM : ℝ → ℂ) (α β : ℂ) (x t : ℝ) (k : ℤ) :
    mixed N d j l a b F1 F2 FM α β x t k =
      ∑ h ∈ hSupport N d, block N d j l a b F1 F2 FM α β x t k h := by
  rw [mixed_row,sum_cutoff d N hd]
  rfl

/-- Every ordered actual branch pair, with the original root cutoff.
The supported h set supplies exactly the arithmetic hypotheses required
by the existing G average; no block norm estimate is asserted here. -/
theorem rectangle_supported (N d j l K : ℕ) (hd : 1 ≤ d) (js : List ℕ) (hK : 0 < K)
    (F1 F2 FM : ℝ → ℂ) (α β : ℂ) (x t : ℝ) (k : ℤ) :
    let bs := branches ⌊Real.rpow (N:ℝ) (K:ℝ)⁻¹⌋₊ K js
    PRZZAStarRectangles.rectangle N d j l
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) F1 F2 FM α β x t k =
      (bs.flatMap (fun b => bs.map (fun c =>
        ∑ h ∈ hSupport N d, block N d j l (coeff b) (coeff c) F1 F2 FM α β x t k h))).sum := by
  dsimp only
  rw [original_branch_pairs N d j l K js hK]
  simp_rw [mixed_supported N d j l hd]

theorem literal_supported (N d K : ℕ) (D H T A B : ℝ) (js : List ℕ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hd : 1 ≤ d) (hK : 0 < K) (hFM : Continuous FM) (hW : Continuous W)
    (hPhi : ContDiff ℝ ∞ Phi) (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (hsM : Function.support FM ⊆ Set.Icc A B)
    (hN : 0 < N) (hT : 0 < T) (hA : 0 < A) (hB : 0 < B) :
    let bs := branches ⌊Real.rpow (N:ℝ) (K:ℝ)⁻¹⌋₊ K js
    PRZZAStar.literal N d D H T (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      F1 F2 FM W Phi alpha beta =
    (1/(2*Real.pi):ℂ)*∫ t : ℝ, ∫ p : ℝ × ℝ,
      (PRZZAStarWindow.window N T A B).indicator
        (fun p : ℝ × ℝ => W (2*Real.pi*p.1/p.2)/((d:ℂ)*(p.1:ℂ)^(alpha+beta))) p *
      mellin Phi (t*Complex.I)*twist (p.1*p.2/T) t *
      (∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
        ∑ k ∈ (frequencies d D H).image freq,
          nu (frequencies d D H) p.1 p.2 k *
          (bs.flatMap (fun b => bs.map (fun c => ∑ h ∈ hSupport N d,
            block N d j l (coeff b) (coeff c) F1 F2 FM alpha beta p.1 t k h))).sum) := by
  dsimp only
  rw [PRZZLiteralBranches.literal_branches N d K D H T A B js F1 F2 FM W Phi alpha beta
    hK hFM hW hPhi hsP hsM hN hT hA hB]
  simp_rw [mixed_supported N d _ _ hd]

#print axioms literal_supported
#print axioms mixed_row
#print axioms mixed_supported
#print axioms rectangle_supported
end XiPrime8845.PRZZSupportedBranches

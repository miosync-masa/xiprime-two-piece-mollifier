import PRZZHBRectangles

/-! The literal A-star integral with all actual ordered HB branch pairs.
This is an equality, with the original strict frequency cutoffs, dyadic
cells, coprimality and d*n cutoffs intact. No h-block estimate is assumed. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory
namespace XiPrime8845.PRZZLiteralBranches
open PRZZHBBranches PRZZHBRectangles PRZZAStarNu PRZZNuCoefficient PRZZMellinSeparation
set_option maxHeartbeats 2000000

theorem literal_branches (N d K : ℕ) (D H T A B : ℝ) (js : List ℕ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hK : 0 < K) (hFM : Continuous FM) (hW : Continuous W)
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
          (bs.flatMap (fun b => bs.map (fun c =>
            mixed N d j l (coeff b) (coeff c) F1 F2 FM alpha beta p.1 t k))).sum) := by
  dsimp only
  rw [literal_mellin_nu N d D H T A B _ F1 F2 FM W Phi alpha beta
    hFM hW hPhi hsP hsM hN hT hA hB]
  simp_rw [signedSum_branches N d K js hK D H F1 F2 FM alpha beta]

#print axioms literal_branches
end XiPrime8845.PRZZLiteralBranches
